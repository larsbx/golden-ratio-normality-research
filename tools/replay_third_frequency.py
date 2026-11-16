"""Independent integer replay for the scheduled mode h=1, spacing=2, lag=1."""

from fractions import Fraction
from math import isqrt
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "tests")]

from oracles.reference import polynomial_certificate, prefix_value
from test_fixed_frequency import SCALE, norm_squared_box, phase_sum_box, transition_count


def check_source_transfer(maximum):
    scale, q, residual = 1, 0, 1
    previous = None
    for n in range(maximum + 1):
        alpha = prefix_value(2, n)
        assert polynomial_certificate(scale, alpha)
        assert q == scale - 1 - alpha
        assert residual == q*q - 3*scale*q + scale*scale
        derivative = 3*scale - 2*q
        branch = sum(3*derivative*j - j*j <= 9*residual for j in (1, 2))
        third = 3*q - scale + branch
        shifted = third*third - 7*scale*third + scale*scale
        assert shifted == 9*residual - 3*derivative*branch + branch*branch
        # Independent floor from sqrt(45): floor((7B - B*sqrt(45))/2).
        assert third == (7*scale - isqrt(45*scale*scale) - 1) // 2
        assert 0 < shifted < 7*scale - 2*third - 1
        assert (2*scale - 3*alpha) - third == 3 - branch
        if previous is not None:
            old_scale, old_third, old_shifted = previous
            digit = third - 2*old_third
            threshold = 2*(7*old_scale - 2*old_third) - 1
            assert digit == int(4*old_shifted >= threshold)
            assert shifted == 4*old_shifted - digit*threshold
        previous = scale, third, shifted
        gap = 2*derivative - 1
        digit = int(4*residual >= gap)
        scale, q, residual = 2*scale, 2*q + digit, 4*residual - digit*gap


def check_carry_suffix(width):
    for n in range(width + 1):
        scale = 1 << n
        q = scale - 1 - prefix_value(2, n)
        bits = tuple(int(bit) for bit in f"{q:0{n}b}") if n else ()
        high = sum(bit * (q >> (i+1)) for i, bit in enumerate(bits))
        suffix = sum(bit * (1 << (n-1-i)) * (q % (1 << (i+1)))
                     for i, bit in enumerate(bits))
        carry = 3*q - scale - high
        assert q*q == scale*high + suffix
        assert suffix - scale*carry == q*q - 3*scale*q + scale*scale


def mean_box(p, n):
    a, b = phase_sum_box(p, n)[0]
    return Fraction(a, SCALE*n), Fraction(b, SCALE*n)


def display_box(box, places=8):
    denominator = 10**places
    a, b = (endpoint * denominator for endpoint in box)
    low = a.numerator // a.denominator
    high = -(-b.numerator // b.denominator)

    def fixed(value):
        sign = "-" if value < 0 else ""
        whole, fraction = divmod(abs(value), denominator)
        return f"{sign}{whole}.{fraction:0{places}d}"

    return f"[{fixed(low)}, {fixed(high)}]"


def correlations(n):
    q = prefix_value(2, n)
    modulus = 1 << n
    assert polynomial_certificate(modulus, q)
    scaled = 3*q % modulus
    phase_count = transition_count(scaled, n)
    beta = (7*modulus - isqrt(45*modulus*modulus) - 1) // 2
    beta_count = transition_count(beta, n)
    correction = 2*modulus - 3*q - beta
    assert 1 <= correction <= 3
    assert beta_count >= (n+1).bit_length() - 2
    # Verify the branch-sensitive beta displacement and paired bounds.
    beta_real = mean_box(beta, n)
    delta = Fraction(44*correction*(modulus-1), 7*n*modulus)
    one, two, three = (mean_box(k*q, n) for k in (1, 2, 3))
    assert phase_sum_box(scaled, n)[0] == phase_sum_box(3*q, n)[0]
    # cos(u)cos(2u) = (cos(u)+cos(3u))/2. Subtract the product of means.
    products = [a*b for a in one for b in two]
    covariance = ((one[0]+three[0])/2 - max(products),
                  (one[1]+three[1])/2 - min(products))
    energy = (2*(1-three[1]), 2*(1-three[0]))
    assert 0 <= energy[0] <= energy[1] <= 4
    assert three[1] <= 1 - Fraction(phase_count, n)
    assert three[1] - beta_real[0] <= delta and beta_real[1] - three[0] <= delta
    assert three[1] <= 1 - Fraction(beta_count, n) + delta
    reverse_constant = 3 + Fraction(22, 7)**2/24
    assert 1 - three[0] <= reverse_constant*Fraction(beta_count+1,n) + delta
    twice_loss = 2*SCALE - isqrt(2*SCALE*SCALE)
    cap = 2*SCALE*n - twice_loss*phase_count
    assert cap > 0 and 4*norm_squared_box(scaled, n)[1] <= cap*cap
    beta_cap = 2*SCALE*n*(1+delta) - twice_loss*beta_count
    assert beta_cap > 0 and 4*norm_squared_box(scaled, n)[1] <= beta_cap*beta_cap
    print(f"{n:>5}  {display_box(three):>26}  {display_box(energy):>26}  "
          f"{display_box(covariance):>26}  {phase_count:>5}")


def check_controls():
    # At n=0 the branch is in {0,1,2}, but the raw quadratic comparison
    # holds for j=10. The upper branch restriction cannot be removed.
    assert 3*3*10 - 10**2 <= 9
    # Varying odd numerators produce a frequency permutation, including zero.
    for n in range(2, 8):
        modulus = 1 << n
        for p in (1, 3, 5, modulus-1):
            assert {h*p % modulus for h in range(modulus)} == set(range(modulus))
    for n in (1024, 4096):
        # A single finite numerator per width; no changing actual source is used.
        square_bits = "".join("1" if isqrt(i)**2 == i else "0" for i in range(1, n+1))
        square = int(square_bits, 2)
        assert mean_box(3*square, n)[0] > Fraction(4, 5)
        print(f"square n={n}: real3={display_box(mean_box(3*square,n))}")
        assert mean_box(3, n)[0] > Fraction(31, 32)  # seed 1/2^n, mode 3
    # One fixed irrational, sampled at stage boundaries. The written argument
    # gives both limits and separation for all starts, not just boundaries.
    for j in (32, 128):
        mixed = "".join("0"*i + "1"*i + "01"*(2*i) for i in range(1, j+1))
        p, n = int(mixed, 2), len(mixed)
        assert all(abs(endpoint) < Fraction(9, j) for endpoint in mean_box(p, n))
        assert mean_box(3*p, n)[0] > 1 - Fraction(20, j)
        print(f"mixed stage {j}: n={n}, real1={display_box(mean_box(p,n))}, "
              f"real3={display_box(mean_box(3*p,n))}")
    # Exact actual prefix refutes the positive unit square-root cap.
    n = 4
    q = prefix_value(2, n)
    assert q == 9
    coefficient = phase_sum_box(3*q, n)[0]
    assert coefficient[1] < 0 and coefficient[1]**2 > n*SCALE*SCALE
    print(f"actual unit square-root cap fails at N={n}; "
          f"Re S3={display_box(tuple(Fraction(v,SCALE) for v in coefficient))}")


def main():
    if not __debug__:
        raise RuntimeError("Run this replay with Python assertions enabled")
    check_source_transfer(2048)
    check_carry_suffix(128)
    print("N       real A3                   mean lag-two energy        cosine covariance          transitions")
    for n in (32, 128, 512, 2048, 8192, 16384, 32768):
        correlations(n)
    center, radius = 32768, 200
    _, upper = phase_sum_box(3*prefix_value(2, center), center)[0]
    assert Fraction(upper, SCALE) + radius + Fraction(132, 7) < 0
    print(f"certified negative real third mode for every width {center-radius}..{center+radius}")
    check_controls()
    print("PASS: exact integer controls and outward-rounded phase bounds")


if __name__ == "__main__":
    main()
