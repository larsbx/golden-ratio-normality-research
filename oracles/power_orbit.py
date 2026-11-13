"""Strict finite power-orbit checker independent of the native state machine.

Fibonacci values and outputs use the existing weighted-sum/isqrt checker.
The complete digit segment is checked separately through a root prefix and
ordinary binary decoding; contiguous counts use the independent slice oracle.
These finite checks do not establish an eventual frequency estimate.
"""

import re

from oracles.reference import block_counts, check_automaton_record, prefix_value, word


def check_power_orbit_record(record: dict) -> None:
    expected = {"schema", "base", "start", "length", "width", "digits", "counts", "inputs"}
    if type(record) is not dict or set(record) != expected:
        raise ValueError("power-orbit record keys")
    if type(record["schema"]) is not str or record["schema"] != "golden-normality-power-orbit-v1":
        raise ValueError("power-orbit schema")
    base, start, length, width = (record[key] for key in ("base", "start", "length", "width"))
    if any(type(value) is not int for value in (base, start, length, width)):
        raise ValueError("power-orbit integer metadata")
    if not (base == 2 and 0 <= start <= 4096 and 0 <= length <= 256
            and start + length <= 4096 and 1 <= width <= 4):
        raise ValueError("power-orbit resource contract")
    text = record["digits"]
    if type(text) is not str or len(text) != length or any(c not in "01" for c in text):
        raise ValueError("power-orbit digit word")
    counts = record["counts"]
    if (type(counts) is not list or len(counts) != 2**width
            or any(type(value) is not int or value < 0 for value in counts)):
        raise ValueError("power-orbit count encoding")
    inputs = record["inputs"]
    if type(inputs) is not list or len(inputs) != length:
        raise ValueError("power-orbit input sequence")

    outputs = []
    for offset, entry in enumerate(inputs):
        if type(entry) is not dict or set(entry) != {"exponent", "value", "fibonacci_digits", "output"}:
            raise ValueError("power-orbit input keys")
        exponent = entry["exponent"]
        if type(exponent) is not int or exponent != start + offset:
            raise ValueError("power-orbit exponent sequence")
        value = entry["value"]
        if type(value) is not str or re.fullmatch(r"0|[1-9][0-9]*", value) is None:
            raise ValueError("canonical power value")
        power = 1 << exponent
        # Validate against the bounded expected decimal without parsing arbitrary input.
        if value != str(power):
            raise ValueError("power-orbit value is not 2^exponent")
        fibonacci_digits = entry["fibonacci_digits"]
        if type(fibonacci_digits) is not str or not 1 <= len(fibonacci_digits) <= 10000:
            raise ValueError("power-orbit Fibonacci word resource contract")
        check_automaton_record({"value": power, "digits": fibonacci_digits,
                                "output": entry["output"]})
        outputs.append(entry["output"])
    if text != "".join(str(value) for value in outputs):
        raise ValueError("power-orbit digit concatenation")

    actual = word(2, start + length, prefix_value(2, start + length))[start:]
    if outputs != actual:
        raise ValueError("power-orbit actual digit segment")
    if counts != block_counts(actual, 2, width) or sum(counts) != max(0, length + 1 - width):
        raise ValueError("power-orbit contiguous counts")
