"""Canonical finite certificates. Arithmetic is the pinned upstream BigZ.

This program is an untrusted certificate producer. Acceptance rechecks its
output with an independent Python oracle and closed Lean propositions.
"""

from std.sys import argv
from finite_exact.bigint_z import (
    BigZ, bigz_zero, bigz_from_i64, bigz_add, bigz_sub, bigz_mul,
    bigz_eq, bigz_lt,
)
from finite_exact.exact_decimal import bigz_decimal


def natural(value: Int) -> BigZ:
    return bigz_from_i64(Int64(value))


def prefix_certificate(scale: BigZ, value: BigZ) -> Bool:
    if scale.sign <= 0 or value.sign < 0:
        return False
    var square = bigz_mul(scale, scale)
    var low = bigz_add(bigz_mul(value, value), bigz_mul(scale, value))
    var successor = bigz_add(value, natural(1))
    var high = bigz_add(bigz_mul(successor, successor), bigz_mul(scale, successor))
    return not bigz_lt(square, low) and bigz_lt(square, high)


struct Prefix(Copyable):
    var scale: BigZ
    var value: BigZ
    var digits: List[Int]

    def __init__(out self):
        self.scale = natural(1)
        self.value = bigz_zero()
        self.digits = List[Int]()


def phi_prefix(base: Int, length: Int) raises -> Prefix:
    if base < 2 or base > 10 or length < 0 or length > 4096:
        raise Error("prefix outside base 2..10 / length 0..4096 contract")
    var result = Prefix()
    var radix = natural(base)
    for _ in range(length):
        result.scale = bigz_mul(result.scale, radix)
        var previous = bigz_mul(result.value, radix)
        var found = False
        for digit in range(base):
            var candidate = bigz_add(previous, natural(digit))
            if prefix_certificate(result.scale, candidate):
                result.value = candidate^
                result.digits.append(digit)
                found = True
                break
        if not found:
            raise Error("no digit satisfies the exact root certificate")
    if not prefix_certificate(result.scale, result.value):
        raise Error("invalid terminal prefix certificate")
    return result^


def block_counts(digits: List[Int], base: Int, width: Int) raises -> List[Int]:
    if base < 2 or base > 10 or width < 1 or width > 4 or len(digits) > 4096:
        raise Error("block count outside bounded allocation contract")
    var capacity = 1
    for _ in range(width):
        capacity *= base  # at most 10^4
    var counts = List[Int](length=capacity, fill=0)
    var window = 0
    for i in range(len(digits)):
        var digit = digits[i]
        if digit < 0 or digit >= base:
            raise Error("digit outside alphabet")
        window = (window * base + digit) % capacity  # below 10^5
        if i + 1 >= width:
            counts[window] += 1  # at most 4096
    return counts^


def zeckendorf(value: BigZ) raises -> List[Int]:
    if value.sign < 0:
        raise Error("negative Fibonacci input")
    if value.is_zero():
        return List[Int](length=1, fill=0)
    var weights = List[BigZ]()
    weights.append(natural(1))
    weights.append(natural(2))
    while not bigz_lt(value, weights[len(weights) - 1]):
        weights.append(bigz_add(weights[len(weights) - 1], weights[len(weights) - 2]))
        if len(weights) > 10000:
            raise Error("Fibonacci representation budget exhausted")
    var remaining = value.copy()
    var digits = List[Int]()
    var started = False
    var previous = 0
    for i in range(len(weights) - 1, -1, -1):
        var digit = 0 if bigz_lt(remaining, weights[i]) else 1
        if digit == 1:
            remaining = bigz_sub(remaining, weights[i])
        if started or digit == 1:
            if previous == 1 and digit == 1:
                raise Error("inadmissible Fibonacci representation")
            digits.append(digit)
            previous = digit
            started = True
    if not remaining.is_zero():
        raise Error("incomplete Fibonacci representation")
    return digits^


def binary_automaton(digits: List[Int]) raises -> Int:
    # Barnoff--Bright--Shallit, Figure 2. State 8 is a rejecting sink.
    var delta: List[Int] = [0, 1, 2, 8, 3, 4, 5, 6, 2, 8, 7, 1, 5, 8, 5, 1, 8, 8]
    var output: List[Int] = [0, 1, 0, 1, 0, 0, 1, 1]
    var state = 0
    for digit in digits:
        if digit < 0 or digit > 1:
            raise Error("nonbinary Fibonacci digit")
        state = delta[2 * state + digit]
    if state == 8:
        raise Error("adjacent ones in Fibonacci input")
    return output[state]


def digit_string(digits: List[Int]) -> String:
    var result = String("")
    for digit in digits:
        result += String(digit)
    return result^


def count_json(counts: List[Int]) -> String:
    var result = String("[")
    for i in range(len(counts)):
        if i > 0:
            result += ","
        result += String(counts[i])
    return result + "]"


def emit_prefix(base: Int, length: Int, width: Int) raises:
    var result = phi_prefix(base, length)
    var counts = block_counts(result.digits, base, width)
    print('{"schema":"golden-normality-prefix-v1","base":' + String(base)
        + ',"length":' + String(length) + ',"scale":"' + bigz_decimal(result.scale)
        + '","value":"' + bigz_decimal(result.value) + '","digits":"'
        + digit_string(result.digits) + '","width":' + String(width)
        + ',"counts":' + count_json(counts) + '}')


def main() raises:
    var args = argv()
    if len(args) != 4:
        raise Error("usage: golden-normality BASE LENGTH BLOCK_WIDTH")
    emit_prefix(Int(args[1]), Int(args[2]), Int(args[3]))
