# Equivalent targets and certified checkpoints

This milestone provides two equivalent formulations of `NormalInBase`, an
exact bound between finite checkpoints, and a conditional route from eventual
checkpoint budgets to normality. It does not establish the required eventual
budgets for the golden ratio.

Write

\[
C_{b,k,j}(N)=\operatorname{occurrences}(b,k,j,N),\qquad
D_{b,k,j}(N)=|b^k C_{b,k,j}(N)-N|.
\]

The implementation uses `Nat.dist` for the absolute difference. The count is
over the first N consecutive starting positions in the actual fractional
digits of alpha = phi-1, including overlapping blocks and leading-zero words.

## 1. Every block value has exactly one word of its width

[`WordEncoding.lean`](../GoldenNormality/WordEncoding.lean) defines a computable
decoder:

\[
\operatorname{wordOfValue}(b,0,j)=[],\qquad
\operatorname{wordOfValue}(b,k+1,j)=
\bigl\lfloor j/b^k\bigr\rfloor::
\operatorname{wordOfValue}(b,k,j\bmod b^k).
\]

Its length is always k. Under b>=2 and j<b^k, every digit is below b and the
positional value is exactly j. Conversely, decoding the value of an alphabet
word at its original width recovers that exact word. The prior injectivity
theorem then gives unique existence for every admissible block value.

Width zero is included: j<b^0 forces j=0 and gives the empty word. For positive
widths, leading zeros are preserved; for example, base ten, width two, value
three decodes to `[0,3]`. The range hypothesis matters: value 100 at width two
decodes to `[10,0]`, which is not a base-ten alphabet word. Width zero discards
an out-of-range positive value, so unqualified value recovery is also false.

## 2. Equivalent normality targets with exact quantifiers

[`NormalityCriteria.lean`](../GoldenNormality/NormalityCriteria.lean) proves

```lean
NormalInBase b ↔ NormalByWords b
NormalInBase b ↔ UniformBlockNormality b
```

`NormalByWords` quantifies over every nonempty alphabet word w and every positive
tolerance denominator T. It requires a positive threshold N0 such that every
N>=N0 satisfies the exact discrepancy inequality for `Blocks.count w` on
`N + w.length - 1` actual digits. The forward direction uses the existing
frequency bridge. The converse uses the new decoder to account for every
j<b^k, including values represented with leading zeros.

For `UniformBlockNormality`, the order is

\[
\forall k\ge1\;\forall T\ge1\;\exists N_0\ge1\;
\forall N\ge N_0\;\forall j<b^k:\quad D_{b,k,j}(N)T\le N.
\]

For fixed k and T there are finitely many j. Induction takes a maximum of their
individual positive thresholds, producing one threshold for all values at that
width and tolerance. Neither k nor T is moved after the existential threshold.
These equivalences reorganize the open target; they do not prove either side.

## 3. Bounds throughout a finite checkpoint interval

[`CheckpointBounds.lean`](../GoldenNormality/CheckpointBounds.lean) first proves
that C(N) is monotone: adding starting positions cannot remove a match. For
L<=N<=R, this gives

\[
\boxed{D(N)\le\max(D(L),D(R))+(R-L).}
\]

To see both sides, monotonicity gives

\[
b^k C(L)\le b^k C(N)\le b^k C(R).
\]

The upper signed deviation is at most D(R)+(R-N); the lower signed deviation
is at most D(L)+(N-L). Both are bounded by the displayed expression. The proof
uses only monotonicity and endpoint arithmetic, with no statistical assumption.

Consequently, the single endpoint budget

\[
\bigl(\max(D(L),D(R))+(R-L)\bigr)T\le L
\]

proves D(N)T<=N for every N in the closed interval [L,R].
`certified_interval_bound` consumes two proved `DigitsAt b 0` prefix bindings
and exact counts for the same pattern. Their lengths determine L and R by
the complete-window formula. Both words therefore refer to prefixes of the
same actual digit sequence.

The gap term is necessary. For the actual first four binary digits `1001`, the
one-symbol pattern `[1]` has D(2)=0, D(3)=1, and D(4)=0. Perfect endpoint
balance alone does not bound the intermediate discrepancy by zero. This
counterexample is compiled, and the stronger false claim is required to fail.

## 4. The conditional infinite criterion

For every valid k,j and every T>=1, suppose there exists a strictly increasing
function q from natural indices to natural checkpoints, and an index i0, such
that for every i>=i0,

\[
\bigl(\max(D(q_i),D(q_{i+1}))+(q_{i+1}-q_i)\bigr)T\le q_i.
\]

`normalInBase_of_checkpoint_bounds` proves that these hypotheses imply
`NormalInBase b` when b>=2. The checkpoint sequence and i0 may depend on k,j,T.

A strictly increasing natural sequence is unbounded. The proof finds the first
checkpoint strictly above each N and hence a covering consecutive interval.
Taking N0=max(1,q(i0)) supplies a positive normality threshold. The finite
interval bound then applies at every later N.

Both parts of the infinite hypothesis are retained: coverage by a strictly
increasing sequence, and a budget on every sufficiently late interval. A
constant sequence q(i)=0 satisfies every endpoint budget vacuously but fails
strict increase and covers no positive N. The gate compiles this vacuity
example and rejects its attempted use as a strictly increasing sequence.
The finite fixture below proves none of these eventual hypotheses.

## 5. Concrete finite interval fixture

The research contract adds the native binary prefix of length 224, retaining
the existing length-256 prefix. At width three, they supply L=222 and R=254
complete starts. The tolerance denominator is T=2, and the gap is 32.

| Pattern | C(222) | C(254) | D(222) | D(254) | Endpoint budget |
| --- | ---: | ---: | ---: | ---: | ---: |
| `000` | 33 | 39 | 42 | 58 | 180 |
| `001` | 30 | 34 | 18 | 18 | 100 |
| `010` | 22 | 26 | 46 | 46 | 156 |
| `011` | 27 | 31 | 6 | 6 | 76 |
| `100` | 30 | 34 | 18 | 18 | 100 |
| `101` | 20 | 24 | 62 | 62 | 188 |
| `110` | 27 | 31 | 6 | 6 | 76 |
| `111` | 33 | 35 | 42 | 26 | 148 |

Each budget is `(max(D(222),D(254))+32)*2` and is at most 222. The native
generator emits eight propositions, each quantifying over every integer
N from 222 through 254 and proving `Nat.dist (8*C(N)) N*2 <= N`. No patterns
are filtered. This covers 33 possible start counts per pattern through the
universal interpolation theorem.

The independent receipt-type generator checks these full interval propositions,
including both endpoint bounds and the quantifier over N. A rejection control
tries to substitute a true endpoint-only fact for the interval theorem; it must
fail with a type mismatch. Interval configuration rejects nonpositive tolerance,
missing prefix references, differing bases or widths, and unordered or zero
lower start counts. Invalid configured budgets are failures.

## 6. Acceptance, replay, and literature scope

Run the full pinned gate in a fresh output directory:

```sh
python3 tools/verify.py --output build/normality-criteria
```

Every project module and every generated receipt/type-check/counterexample
module is rebuilt and audited. The explicit wrappers in `Contracts.lean` fix
the full public types, including all quantifiers in the conditional criterion.
As before, an observed report names the exact accepted source revision and
hashes; the claim ledger is not execution evidence.

The proportional literature check used Kozachinskiy and Shen,
[*Automatic Kolmogorov complexity, normality and finite state dimension
revisited*, arXiv:1701.09060v6](https://arxiv.org/abs/1701.09060v6), especially
Sections 3.1 and 4.1 on normal sequences and non-aligned block counts.
The word/value reformulation, finite maximum of thresholds, and monotone-count
interpolation here are elementary proof interfaces; no new normality result
for algebraic irrationals or priority claim is made. The aligned/non-aligned
equivalence and stronger literature criteria are not newly formalized here.
