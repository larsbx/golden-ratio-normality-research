# Total evaluation on the binary power orbit

This milestone connects the verified binary automaton to a total computable
sequence and to the exact all-block normality target. It also provides a native
producer whose finite traces retain the input power at every position. The
remaining obligation is an eventual frequency estimate for this sequence.

## 1. A total input encoder

[`ZeckendorfEncoding.lean`](../GoldenNormality/ZeckendorfEncoding.lean) converts
mathlib's Zeckendorf representation into the Boolean word format consumed by
the automaton. Mathlib supplies a descending list of Fibonacci indices, each
at least two, with consecutive entries separated by at least two. Their
Fibonacci values sum to the requested natural number.

The conversion recursively encodes the lower indices. For a head index a and
an already encoded tail r, it prepends a true bit and enough false bits to
make that leading bit have weight F_a. The proof establishes the tail-length
bound before using natural subtraction for the padding. If a further true bit
exists, the index gap guarantees at least one intervening false bit.

The public contracts are

```lean
encode (q : Nat) : List Bool
encode_admissible (q : Nat) : Admissible (encode q)
fibonacciSum_encode (q : Nat) : fibonacciSum (encode q) 2 = q
```

They hold for every natural q, including zero, whose encoded word is empty.
The least significant position has weight F_2=1. This is a proved conversion
of the pinned dependency's representation, with no new uniqueness or
minimality claim about the native implementation.

## 2. From total evaluation to every actual block

[`PowerOrbit.lean`](../GoldenNormality/PowerOrbit.lean) defines

```lean
evaluated q := (classify (encode q)).getD 0
powerDigit n := evaluated (2^n)
```

The default value in `getD` is proved unreachable: admissibility implies that
the classifier returns `some (evaluated q)`. Its output is below two, and the
existing real invariant supplies its exact arithmetic meaning.

Writing alpha=phi-1, the universal digit identity is

\[
\operatorname{powerDigit}(n)
=\lfloor 2^{n+1}\alpha\rfloor-2\lfloor2^n\alpha\rfloor.
\]

The implementation states this as an equality in the integers. `powerDigits
start length` collects consecutive outputs while retaining the starting
position. For every natural start and length, Lean proves

```lean
DigitsAt 2 start (powerDigits start length)
powerDigits start length = actualDigits 2 start length
(wordValue 2 (powerDigits start length) : Int) = blockValue 2 start length
```

For every nonempty binary alphabet word w and every N, the frequency bridge
therefore gives

\[
\operatorname{Blocks.count}\bigl(w,
  \operatorname{powerDigits}(0,N+|w|-1)\bigr)
=\operatorname{occurrences}(2,|w|,\operatorname{wordValue}(2,w),N).
\]

All N consecutive starting positions are counted, including overlapping blocks
and blocks with leading zeros. The prefix length remains N+|w|-1.

`PowerOrbitNormality` states the full eventual bound on these computable words:
for every nonempty binary word w and every positive integer T, there is a
positive N0 such that every N>=N0 satisfies

\[
\left|2^{|w|}\operatorname{Blocks.count}
  \bigl(w,\operatorname{powerDigits}(0,N+|w|-1)\bigr)-N\right|T\le N.
\]

The proved equivalence is

```lean
PowerOrbitNormality <-> NormalInBase 2
```

The threshold may depend on w and T. Total computability supplies neither a
threshold nor a discrepancy estimate; the equivalence preserves that open
obligation.

## 3. Certifying arbitrary native representations

Finite receipt checking does not reduce the canonical encoder at large powers.
Instead, the recursive proposition `PowerOrbitAt start inputs outputs` requires
each supplied Fibonacci word to have value 2^(start+offset), and the verified
classifier to return the corresponding supplied digit. The input and output
lists must end together. Both empty lists are valid; unequal lengths are false.

This relation proves all three facts:

```lean
inputs.length = outputs.length
DigitsAt 2 start outputs
outputs = powerDigits start outputs.length
```

Representations may contain leading zeros and need not equal `encode`. The
last equality follows through the shared actual-digit semantics. It avoids
both a native-encoder equivalence assumption and expensive reduction of the
reference encoder.

The occurrence corollary explicitly requires `PowerOrbitAt 0 inputs outputs`.
A trace beginning at another position certifies that actual segment, while a
first-N occurrence count requires a prefix beginning at zero. Source position
is never erased during receipt translation.

## 4. Actual native execution and its bounded checker

[`kernel/power_orbit.mojo`](../kernel/power_orbit.mojo) accepts
`START LENGTH BLOCK_WIDTH`. It constructs 2^START by repeated doubling in the
pinned upstream BigZ type and doubles once per subsequent digit. It reuses
the existing Fibonacci encoder, automaton, and overlapping-window counter.
Powers are never narrowed to a machine integer.

The bounded native contract is base two, 0<=START<=4096, 0<=LENGTH<=256,
START+LENGTH<=4096, and block width 1..4. Metadata operands are bounded before
the end calculation, so signed overflow cannot make a huge start admissible.
These bounds limit this executable; they do not restrict the universal Lean
encoder or digit identities.

Each record contains the source start and length, output word, complete
histogram, and one entry per exponent. Every entry retains its exponent,
canonical decimal power, Fibonacci word, and classifier output.

The [independent checker](../oracles/power_orbit.py) validates:

- Exact schemas, actual integer types, resource bounds, and consecutive exponents.
- Canonical decimal values equal to the specific 2^exponent, even when an
  alternative value has a perfectly valid classifier output.
- The Fibonacci value by an independent least-significant weighted sum,
  admissibility, and the output by integer-square-root arithmetic.
- The complete actual digit segment through an independently computed root
  prefix, followed by all contiguous counts using slices.

Fibonacci text is bounded by the native 10,000-symbol budget before expensive
representation checking. Leading zeros within that budget remain allowed.
The checker contains no copy of the native automaton or Fibonacci encoder.

The research contract exercises these six cases:

| Start | Digits | Block width | Complete windows |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 3 | 0 |
| 0 | 1 | 3 | 0 |
| 0 | 3 | 3 | 1 |
| 0 | 128 | 3 | 126 |
| 17 | 8 | 2 | 7 |
| 64 | 4 | 2 | 3 |

The main fixture uses powers from 2^0 through 2^127. Its width-three histogram,
in value order 000 through 111, is `[16,15,9,18,16,12,18,22]`. The shifted
fixtures are `11110011` at start 17 and `1111` at start 64. These finite
observations are retained with exact source bindings; no eventual frequency
estimate is inferred from them.

## 5. Exact receipt types and false-inference controls

For every input, the translator emits separate value, classifier-output, and
actual-digit theorems. Every trace also receives its `PowerOrbitAt` proof,
actual-digit binding, and equality to the canonical output segment. All
patterns receive list-count, actual-segment-count, and canonical-segment-count
theorems. Only zero-start traces receive occurrence and discrepancy theorems.

For these six cases that is 634 new receipt theorems. Every one receives an
independent exact-type wrapper generated from the fixed contract and the root
and slice oracle, without reading the native transcript or its translator.
The expected types retain literal positions, lengths, powers, digits, patterns,
and complete-start expressions.

The compiled positive controls retain empty traces, leading-zero input words,
and correctly shifted segments. Rejection controls cover wrong power values,
shifted exponents, unequal trace lengths, wrong outputs, ordinal inputs used in
place of powers, a shifted segment presented as a prefix, and a one-way
implication offered in place of the normality equivalence.

A concrete distinction is visible at the first four inputs: applying the
classifier to representations of 1,2,3,4 yields `1010`; the required inputs
1,2,4,8 yield the actual binary prefix `1001`. Valid evaluations on ordinary
integer inputs therefore do not certify the intended power orbit.

Run the full gate in a fresh directory after installing the pinned dependencies:

```sh
python3 tools/verify.py --output build/power-orbit-acceptance
```

The gate rebuilds all project modules and actual native producers, checks every
receipt type and transitive assumption, and requires the rejection controls to
fail for their intended reasons. Native compiler scratch space uses a temporary
directory on the project volume and is removed after compilation. The evidence
packet identifies the exact accepted source and all observed results.

## 6. Literature and remaining scope

The proportional primary-source check revisited Barnoff, Bright, and Shallit,
[*Computing the base-b representation of quadratic irrationals using
automata*](https://cs.uwaterloo.ca/~cbright/reports/digits-automata.pdf),
Theorem 1, Section 2.1, and Figure 2. The published result uses representations
of b^n for the nth base-b digit; the source sequence is part of the theorem.
The encoder reuses
[mathlib's pinned Zeckendorf development](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Data/Nat/Fib/Zeckendorf.lean).

This milestone formalizes the application and its proof interfaces. It makes
no priority claim for the automaton or representation theorem. The total Lean
encoder is proved independently of the Mojo encoder; finite checked traces
do not establish universal native/compiler refinement or a complexity bound
for the reference encoder. Distribution of the actual power-orbit outputs,
with every required block and eventual quantifier, remains to be established.
