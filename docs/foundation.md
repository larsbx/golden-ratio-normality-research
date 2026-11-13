# The finite foundation and the open asymptotic obligation

## 1. An exact root certificate

Write α = φ−1 = (√5−1)/2. The Lean development proves
`0 < α < 1` and `α²+α=1` from the real square root definition.
For natural numbers B and q, define

\[
  \operatorname{Cert}(B,q)\iff q^2+Bq\leq B^2
    <(q+1)^2+B(q+1).
\]

For every **B > 0**, the central theorem is

\[
  \operatorname{Cert}(B,q)\iff q=\lfloor B\alpha\rfloor.
\]

The polynomial `x²+Bx` is strictly increasing for nonnegative x when B>0,
and its value at Bα is B². Thus the two inequalities locate Bα in `[q,q+1)`.
This is a universal proof about the explicit real number, not a numerical
approximation to √5. The separate executable checker includes B>0.

The signed residual E = B²−q²−Bq gives the equivalent condition
`0 ≤ E < 2q+B+1`. Appending a digit d in base b sends B to bB and q to bq+d,
with the exact identity

\[
 E'=b^2E-bd(2q+B)-d^2.
\]

`Prefix.lean` proves both equivalence and the update identity. The first
native implementation searches the original inequalities; the residual
identity is available for a later implementation without changing the contract.

## 2. Digits, consecutive blocks, and finite word binding

Let q_n = floor(b^n α). The zero-indexed fractional digit is
`d_n=q_(n+1)−bq_n`. A length-k block beginning at n has integer value

\[
 q_{n+k}-b^kq_n
   =\left\lfloor b^k\{b^n\alpha\}\right\rfloor.
\]

The proof supplies its range and concatenation law. In particular, this is
a fixed-width block value: leading zeros are retained by specifying k.

The finite receipt pipeline does not merely attach a mathematical label to
a native string. For every supplied word it reconstructs its successive
integer prefixes and generates a closed Lean root certificate for each one.
`digit_of_certificates` then proves every supplied symbol equals the actual
digit. The conjunction `DigitsAt b start text` binds the whole word, and
`digitsAt_eq_actualDigits` proves equality to the word defined from the real
digit function.

`Blocks.count` advances its start by one symbol, so overlapping occurrences
are included. It is proved equal to an independent enumeration of every
starting position. A match must fit completely in the available suffix.
For a nonempty pattern w of length k,

\[
 \operatorname{count}(w,L\mathbin{+\!+}R)
 =\operatorname{count}(w,L)+\operatorname{count}(w,R)
   +\operatorname{boundaryCount}(w,L,R).
\]

The boundary term needs at most the last k−1 symbols of L and the first k−1
of R. This result holds for arbitrary finite lists with decidable equality,
including short chunks. The library assigns count zero to an empty pattern;
normality quantifies only over positive block lengths.

`certified_count_sound` combines the proved word binding and a checked
numeral count into a theorem about enumerated occurrences in the actual
digit segment. This avoids trusting the certificate translator: an incorrect
translated fact still has to pass the Lean kernel.

The subsequent [block-frequency bridge](block-frequency-bridge.md) proves
that this same list count equals `occurrences`, the function used by
`NormalInBase`. For a nonempty alphabet word of length k and a prefix of
length L, it counts exactly `max(0,L+1−k)` starts. Every generated pattern
receipt now certifies both this mathematical occurrence count and its exact
finite discrepancy `Nat.dist (b^k * count) N`.

## 3. Universal verification of the published binary automaton

The transition table is Figure 2 of Barnoff–Bright–Shallit,
[*Computing the base-b representation of quadratic irrationals using automata*](https://cs.uwaterloo.ca/~cbright/reports/digits-automata.pdf),
TCS 1071 (2026), 115843. Its eight live states and thirteen valid transitions
are prior art. A ninth sink state makes rejection total in the implementation.

Fibonacci words are read most significant first. Their least significant
weights are F₂=1, F₃=2, F₄=3, … . The accepted language excludes adjacent
ones and permits leading zeros. This is a Fibonacci representation of an
integer input, not a base-φ expansion of φ.

The Lean proof tracks an integer pair (q,r) whose coordinates are the word's
Fibonacci value and the value with every weight shifted once. Reading a bit
d transforms it into

\[
  (q,r)\longmapsto(r+d,\;q+r+2d).
\]

For e=r−φq, the real update is `e' = −αe + α²d`. The state invariant is:

| State | Invariant for e | Output |
| --- | --- | --- |
| 0 | e=0 | 0 |
| 1 | α/2 < e < 1/2 | 1 |
| 2 | −α² < e < −α²/2 | 0 |
| 3 | α³/2 < e < α³ | 1 |
| 4 | 1/2 < e < α | 0 |
| 5 | −α²/2 < e < 0 | 0 |
| 6 | α³ < e < α/2 | 1 |
| 7 | 0 < e < α³/2 | 1 |

Every valid transition preserves these open intervals. The output depends on
the exact position relative to 0 and 1/2. Consequently, for **every accepted
finite input word** of value q, the output is

\[
 A(Z(q))=\lfloor2q\alpha\rfloor-2\lfloor q\alpha\rfloor.
\]

The integer contribution from φ=α+1 cancels, giving the usual equivalent
formula with φ. If the word's separately checked Fibonacci value is 2^n,
the output is the actual binary digit d_n. The code proves these facts
universally; the 128 native receipts test a finite set of native executions.

The universal theorem consumes an explicit word and its value equality. It
does not claim universal refinement of the native greedy encoder. A future
adapter can connect a total formally verified Zeckendorf encoder to this
already proved word semantics.

## 4. Executable boundaries and independence

Mojo is the canonical producer. Exact integers come from the pinned
[`finite-math-kernels`](https://github.com/larsbx/finite-math-kernels/tree/3573dc4318f4d5ccd6a103b470dc82bed1f798a8)
submodule, with no local arithmetic fork. The producer appends candidate
digits and accepts them by the root inequalities. It counts blocks with a
rolling window. Its explicit bounds are bases 2–10, length 0–4096, and
width 1–4: at most 10,000 histogram entries, rolling intermediates below
100,000, and counts at most 4096. Prefix arithmetic uses BigZ.

The Python oracle uses a different construction:

\[
  \lfloor B\alpha\rfloor
   =\left(\operatorname{isqrt}(5B^2)-B\right)\mathbin{//}2.
\]

Taking the integer square root first is exact here: the discarded part is
less than one, and dividing an integer plus that part by two cannot cross
the next integer boundary. The oracle counts by direct consecutive slices
and evaluates Fibonacci words by an independent least-significant weighted
sum. It rejects malformed types, including booleans used as integers,
noncanonical integer strings, mismatched source metadata, invalid alphabets,
and altered count distributions even when their total is unchanged.

The full gate compiles actual native executables, checks their receipts,
generates closed Lean obligations, compiles those obligations, and audits
the compiled declarations. It accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. Explicit wrapper declarations
in `Contracts.lean` fix the public theorem types. Rejection controls include
false root, scattered-count, and inadmissible-word claims, plus an actual
compiled axiom injection which the compiled audit must reject.

Source hashes, dependency revisions, tool versions, native binary hashes,
logs, and generated propositions are recorded. Project proof objects are
rebuilt into a fresh output directory. Pinned upstream compiled dependencies
are reused; independently rechecking all of mathlib or proving correctness
of the compilers is outside this milestone's trust boundary.

The runner sets `MODULAR_TELEMETRY_ENABLED=false` and
`MODULAR_CRASH_REPORTING_ENABLED=false` before every Mojo invocation, following
the [SDK FAQ](https://mojolang.static.modular.com/nightly/docs/faq/) and
[release documentation](https://github.com/modular/modular/blob/main/Mojo/docs/site/releases/v1.0.0.md).
CI calls the installed Python and Mojo binaries directly, without executing
the pinned Conda package's separate first-activation telemetry hook. The two
disabled settings are included in the native evidence record.

## 5. What remains open

For C_(b,k,j)(N), the number of occurrences of block value j among the first N
starting positions, normality requires convergence to b^(−k) for **every**
k≥1 and j<b^k. The exact rational formulation in `Normality.lean` is

\[
 \forall k\geq1\;\forall j<b^k\;\forall T\geq1\;
 \exists N_0\geq1\;\forall N\geq N_0:\quad
   |b^k C_{b,k,j}(N)-N|\,T\leq N.
\]

The discrepancy uses `Nat.dist`; a negative difference is never lost through
truncated natural subtraction. The threshold may depend on k,j,T. The
definition is a target, with no theorem that it holds for φ in any base.

The exact automaton bridge leaves a specific distribution problem: control
the output block frequencies along **the particular inputs Z(b^n)**.
Uniform sampling of all admissible Fibonacci words, an attractive stationary
distribution, a finite histogram, or a generic almost-everywhere theorem
does not prove that this orbit has the required frequencies. Any future
claim must state precisely which input sequence is controlled and how its
quantifiers imply the target above.

The [literature gate](literature-gate.md) records the relevant prior results,
including a possible uniform upper-frequency criterion. There is no claimed
estimate filling that gap in this milestone.
