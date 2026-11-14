"""Finite witnesses for the automaton on the actual inputs 2^n.

Powers remain in the pinned upstream BigZ representation. This producer is
untrusted; acceptance checks the transcript independently and binds it in Lean.
"""

from std.sys import argv
from finite_exact.bigint_z import bigz_add
from finite_exact.exact_decimal import bigz_decimal
from foundation import (
    natural, zeckendorf, binary_automaton, block_counts, digit_string, count_json,
)


def emit_power_orbit(start: Int, length: Int, width: Int) raises:
    # Bound each operand before checking their sum, avoiding machine overflow.
    if start < 0 or start > 4096 or length < 0 or length > 256 or width < 1 or width > 4:
        raise Error("power orbit outside start 0..4096 / length 0..256 / width 1..4 contract")
    if length > 4096 - start:
        raise Error("power orbit outside end <=4096 contract")

    var power = natural(1)
    for _ in range(start):
        power = bigz_add(power, power)

    var outputs = List[Int]()
    var inputs = String("[")
    for i in range(length):
        var fibonacci_digits = zeckendorf(power)
        var output = binary_automaton(fibonacci_digits)
        outputs.append(output)
        if i > 0:
            inputs += ","
        inputs += '{"exponent":' + String(start + i)
            + ',"value":"' + bigz_decimal(power)
            + '","fibonacci_digits":"' + digit_string(fibonacci_digits)
            + '","output":' + String(output) + '}'
        power = bigz_add(power, power)
    inputs += "]"

    var counts = block_counts(outputs, 2, width)
    print('{"schema":"golden-normality-power-orbit-v1","base":2,"start":'
        + String(start) + ',"length":' + String(length) + ',"width":' + String(width)
        + ',"digits":"' + digit_string(outputs) + '","counts":' + count_json(counts)
        + ',"inputs":' + inputs + '}')


def main() raises:
    var args = argv()
    if len(args) != 4:
        raise Error("usage: golden-normality-power-orbit START LENGTH BLOCK_WIDTH")
    emit_power_orbit(Int(args[1]), Int(args[2]), Int(args[3]))
