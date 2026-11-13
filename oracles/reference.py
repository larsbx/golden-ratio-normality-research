"""Independent unbounded-integer oracle and strict finite record checker.

The producer searches polynomial inequalities; this oracle uses integer sqrt.
The producer rolls a window; this oracle slices each consecutive window.
Neither computation asserts an asymptotic normality result.
"""
from math import isqrt
import re


def prefix_value(base: int, length: int) -> int:
    if type(base) is not int or type(length) is not int or base < 2 or length < 0:
        raise ValueError("invalid base/length")
    scale = base**length
    return (isqrt(5 * scale * scale) - scale) // 2


def polynomial_certificate(scale: int, value: int) -> bool:
    return (scale > 0 and value >= 0
            and value * value + scale * value <= scale * scale
            < (value + 1)**2 + scale * (value + 1))


def encode(base: int, digits: list[int]) -> int:
    value = 0
    for digit in digits:
        if type(digit) is not int or not 0 <= digit < base:
            raise ValueError("invalid digit")
        value = base * value + digit
    return value


def word(base: int, length: int, value: int) -> list[int]:
    result = [0] * length
    for i in range(length - 1, -1, -1):
        value, result[i] = divmod(value, base)
    if value:
        raise ValueError("value does not fit word")
    return result


def block_counts(digits: list[int], base: int, width: int) -> list[int]:
    if width < 1:
        raise ValueError("empty block")
    counts = [0] * base**width
    for i in range(max(0, len(digits) - width + 1)):
        counts[encode(base, digits[i:i + width])] += 1
    return counts


def check_record(record: dict) -> None:
    expected = {"schema", "base", "length", "scale", "value", "digits", "width", "counts"}
    if type(record) is not dict or set(record) != expected:
        raise ValueError("record keys")
    if record["schema"] != "golden-normality-prefix-v1":
        raise ValueError("schema")
    b, n, k = (record[x] for x in ("base", "length", "width"))
    if any(type(x) is not int for x in (b, n, k)):
        raise ValueError("integer metadata")
    if not (2 <= b <= 10 and 0 <= n <= 4096 and 1 <= k <= 4):
        raise ValueError("resource contract")
    for key in ("scale", "value"):
        if type(record[key]) is not str or not re.fullmatch(r"0|[1-9][0-9]*", record[key]):
            raise ValueError("canonical integer")
    scale, value = int(record["scale"]), int(record["value"])
    if scale != b**n or not polynomial_certificate(scale, value):
        raise ValueError("root certificate")
    if value != prefix_value(b, n):
        raise ValueError("independent prefix oracle")
    text = record["digits"]
    if type(text) is not str or len(text) != n or any(c not in "0123456789" for c in text):
        raise ValueError("digit word")
    digits = [int(c) for c in text]
    if encode(b, digits) != value:
        raise ValueError("digit value")
    expected_counts = block_counts(digits, b, k)
    counts = record["counts"]
    if type(counts) is not list or any(type(x) is not int or x < 0 for x in counts):
        raise ValueError("count encoding")
    if counts != expected_counts or sum(counts) != max(0, n - k + 1):
        raise ValueError("contiguous counts")


def fibonacci_value(digits: list[int]) -> int:
    # Independent least-significant weighted sum, not the Lean stream pair.
    weights = [1, 2]
    while len(weights) < len(digits):
        weights.append(weights[-1] + weights[-2])
    return sum(d * weights[i] for i, d in enumerate(reversed(digits)))


def check_automaton_record(record: dict) -> None:
    if type(record) is not dict or set(record) != {"value", "digits", "output"}:
        raise ValueError("automaton keys")
    q, text, digit = record["value"], record["digits"], record["output"]
    if type(q) is not int or q < 0 or type(digit) is not int or digit not in (0, 1):
        raise ValueError("automaton integer")
    if type(text) is not str or not text or any(c not in "01" for c in text) or "11" in text:
        raise ValueError("Fibonacci word")
    if fibonacci_value([int(c) for c in text]) != q:
        raise ValueError("Fibonacci value")
    def floor_phi(value: int) -> int:
        return (isqrt(5 * value * value) + value) // 2
    if digit != floor_phi(2 * q) - 2 * floor_phi(q):
        raise ValueError("automaton output")
