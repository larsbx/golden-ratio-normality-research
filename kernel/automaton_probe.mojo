"""Finite native witness transcript for the universally modeled automaton."""
from foundation import natural, zeckendorf, binary_automaton, digit_string

def main() raises:
    for q in range(128):
        var digits = zeckendorf(natural(q))
        print('{"value":' + String(q) + ',"digits":"' + digit_string(digits)
            + '","output":' + String(binary_automaton(digits)) + '}')
