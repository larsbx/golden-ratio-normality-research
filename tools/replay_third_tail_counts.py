"""Integer replay of signed folded-tail counts for the frequency-three bound."""

from collections import Counter
from fractions import Fraction
from math import isqrt

from replay_third_frequency import SCALE, display_box, mean_box, phase_sum_box, prefix_value


def beta_floor(width):
    scale = 1 << width
    return (7*scale - isqrt(45*scale*scale) - 1) // 2


def reaches_cutoff(residual, derivative, numerator, denominator):
    return numerator*denominator*derivative - numerator**2 <= denominator**2*residual


def check_quadratic_comparisons(starts):
    """Compare residual tests with independently certified prefix differences."""
    last = starts + 9
    prefix = beta_floor(last)
    count = 0
    for n in range(starts):
        scale = 1 << n
        floor = prefix >> (last - n)
        derivative = 7*scale - 2*floor
        residual = floor*floor - 7*scale*floor + scale*scale
        for denominator in (1, 2, 3, 5, 17, 32, 128, 512):
            # Use the quadratic's exact floor at scale denominator * 2^n.
            enlarged = denominator * scale
            exact = (7*enlarged - isqrt(45*enlarged*enlarged) - 1) // 2
            threshold = exact - denominator*floor
            for numerator in (0, max(0, threshold-1), threshold, threshold+1, denominator):
                assert reaches_cutoff(residual, derivative, numerator, denominator) == (
                    numerator <= threshold
                )
                count += 1
    return count


def signed_tail_bins(starts, depth):
    """Count equal and unequal neighboring digits in each closed folded cell."""
    grid = 1 << depth
    prefix = beta_floor(starts + depth)
    bits = f"{prefix:0{starts + depth}b}"
    word = int(bits[1:depth+1], 2)
    equal = [0] * (grid//2)
    unequal = [0] * (grid//2)
    for n in range(starts):
        bucket = min(word, grid-1-word)
        counts = equal if bits[n] == bits[n+1] else unequal
        counts[bucket] += 1
        if n+1 < starts:
            word = (2*word + int(bits[n+depth+1])) & (grid-1)
    assert sum(equal) + sum(unequal) == starts
    return equal, unequal


def cosine_grid(depth):
    """Outward integer bounds for cos(pi*j/2^depth) including endpoints."""
    half = 1 << (depth-1)
    result = [(SCALE, SCALE)]
    for j in range(1, half):
        first = phase_sum_box(j, depth+1)[0]
        rest = phase_sum_box(j, depth)[0]
        result.append((max(0, first[0]-rest[1]), min(SCALE, first[1]-rest[0])))
    result.append((0, 0))
    return result


def bracket(starts, depth):
    equal, unequal = signed_tail_bins(starts, depth)
    cosine = cosine_grid(depth)
    lower = upper = cumulative = 0
    largest = 0
    for j, (plus, minus) in enumerate(zip(equal, unequal)):
        lo_left, hi_left = cosine[j]
        lo_right, hi_right = cosine[j+1]
        lower += plus*lo_right - minus*hi_left
        upper += plus*hi_left - minus*lo_right
        cumulative += plus-minus
        largest = max(largest, cumulative)
    assert lower <= upper
    actual = Fraction(lower, SCALE*starts), Fraction(upper, SCALE*starts)
    displacement = Fraction(132, 7*starts)
    modular = actual[0]-displacement, actual[1]+displacement
    return actual, modular, Fraction(largest, starts)



def direct_modular_bracket(starts, depth):
    """Cross-check the high-width modular sign from the original alpha prefix."""
    grid = 1 << depth
    numerator = (3*prefix_value(2, starts)) % (1 << starts)
    bits = f"{numerator:0{starts}b}" + "0"*(depth-1)
    word = int(bits[:depth], 2)
    counts = [0] * (grid//2)
    for n in range(starts):
        counts[min(word, grid-1-word)] += 1
        if n+1 < starts:
            word = (2*word + int(bits[n+depth])) & (grid-1)
    positive = cosine_grid(depth-1)
    negative = [(-hi, -lo) for lo, hi in reversed(positive[:-1])]
    cosine = positive + negative
    lower = sum(count*cosine[j+1][0] for j, count in enumerate(counts))
    upper = sum(count*cosine[j][1] for j, count in enumerate(counts))
    return Fraction(lower, SCALE*starts), Fraction(upper, SCALE*starts)


def check_parity_control():
    """Enumerate local laws; the infinite construction uses the written proof."""
    for length in (4, 6, 8, 10, 12):
        desired_sign = (-1)**(length//2 + 1)
        words = [x for x in range(1 << length) if (-1)**x.bit_count() == desired_sign]
        assert len(words) == 1 << (length-1)
        assert {(1 << length)-1-x for x in words} == set(words)
        assert len({x % 3 for x in words}) >= 2
        for removed in range(length):
            mask = (1 << removed)-1
            projection = {(x & mask) | ((x >> (removed+1)) << removed) for x in words}
            assert len(projection) == len(words)

        # Three lifted points over a midpoint in each dyadic y-cell. The
        # preimage dyadic partition changes only at endpoints of those cells.
        for depth in range(1, length):
            scale = 1 << depth
            lifts = Counter((2*scale*k-(2*j+1)) // 6
                            for j in range(scale) for k in (1, 2, 3))
            assert lifts == {j: 3 for j in range(scale)}
        analytic_lower = Fraction(1, 2*length*(1 << (length*(length-1)//2)))
        print(f"parity length {length:>2}: all proper marginals fair, lift mixes, "
              f"limiting real third mode >= {analytic_lower}")


def main():
    if not __debug__:
        raise RuntimeError("Run this replay with Python assertions enabled")
    assert reaches_cutoff(residual=1, derivative=7, numerator=8, denominator=1)
    comparisons = check_quadratic_comparisons(256)
    print(f"{comparisons} exact residual comparisons against scaled floors")
    print(" starts    k         actual mean enclosure           modular enclosure         positive cumulative max")
    certified_negative = []
    for starts, depth in ((128, 8), (1024, 10), (8192, 10), (32768, 11),
                          (131072, 12), (524288, 12), (1048576, 14)):
        actual, modular, largest = bracket(starts, depth)
        if starts <= 32768:
            independent = mean_box(3*prefix_value(2, starts), starts)
            assert modular[0] <= independent[0] <= independent[1] <= modular[1]
        if modular[1] < 0:
            certified_negative.append(starts)
        print(f"{starts:>7} {depth:>4} {display_box(actual):>29} "
              f"{display_box(modular):>28} {display_box((largest, largest)):>26}")
    assert {32768, 524288} <= set(certified_negative)
    center, radius = 1048576, 256
    assert starts == center and center*modular[0] > radius + Fraction(132, 7)
    direct = direct_modular_bracket(center, 15)
    assert 0 < direct[0] <= modular[1] and modular[0] <= direct[1]
    print(f"direct modular cross-check at {center}: {display_box(direct)}")
    print(f"certified positive modular real mean at every width {center-radius}..{center+radius}")
    # Concrete witness against requiring every cumulative bin to have a
    # nonpositive signed count, even when the upper Fourier bound is negative.
    actual, modular, largest = bracket(1024, 10)
    assert modular[1] < 0 and largest > 0
    check_parity_control()
    print("PASS: exact floor comparisons, Fourier enclosures and local control checks")


if __name__ == "__main__":
    main()
