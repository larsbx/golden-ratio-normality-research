# A proved lower bound on binary one counts

For every natural number `N`, let

\[
s_N=\operatorname{occurrences}(2,1,1,N).
\]

This counts the one symbols at positions `0` through `N-1` in the fractional
binary expansion of `alpha = phi - 1`. The theorem is

\[
\boxed{2N\le s_N^2+3s_N+4.}
\]

`GoldenNormality.binary_occurrences_ones_bound` states this without any
normality or unproved distribution hypothesis. The corresponding theorem for
the total computable evaluator is `binary_power_ones_bound`, using
`Blocks.count [1] (BinaryAutomaton.powerDigits 0 N)`. The statements include
`N=0` and all later prefix lengths.

This is a square-root-scale sparsity bound. It rules out a binary expansion
whose one count stays bounded, but it does not give positive limiting density,
the limiting frequency `1/2`, or an estimate for every block. Normality in bases
two and ten remains an open claim in the ledger. No novelty claim is made for
the arithmetic argument.

## Exact arithmetic derivation

Set `B=2^N` and let `q` satisfy `PrefixCertificate B q`. Thus

\[
q^2+Bq\le B^2<(q+1)^2+B(q+1).
\]

The existing root theorem identifies this `q` with `floor(B*alpha)` and gives
`q<B`. Write `S=q^2+Bq`. Because `B` is a power of two, it is nonzero modulo
three. For either possible residue of `B`, none of the three residues of `q`
solves `q^2+Bq=B^2`. The lower certificate inequality is therefore strict.
Combining the upper certificate inequality with `q<B` gives

\[
B^2<S+4B,\qquad S<B^2.
\]

For `N>=2`, the numbers `B^2` and `4B` equal
`2^(N-2)*2^(N+2)` and `2^(N+2)`. It follows that

\[
\left\lfloor\frac{S}{2^{N+2}}\right\rfloor=2^{N-2}-1.
\]

This quotient has exactly `N-2` one bits. Dropping low bits cannot increase the
number of one bits, so its binary weight is at most that of `S`.

The upstream definition is
`FiniteMathKernels.binaryWeight q = (Nat.digits 2 q).sum`. If `s` denotes this
weight, binary carry and shift lemmas give

\[
W(S)\le W(q^2)+W(2^Nq)=W(q^2)+s.
\]

The additional square estimate is

\[
2W(q^2)\le s(s+1).
\]

Its proof uses binary induction. Even inputs are shifts. For an odd input,
`(2r+1)^2=4(r^2+r)+1`; subadditivity bounds the weight of `r^2+r`, and the
inductive hypothesis supplies the triangular coefficient. This argument
accounts for carries and does not assume that distinct contributions occupy
distinct bit positions.

Putting these inequalities together gives
`2*(N-2)<=s^2+3*s`, hence the displayed result. The remaining cases `N<2` are
immediate in natural-number arithmetic. The proof does not evaluate a long
digit prefix or infer an infinite assertion from samples.

## Binding arithmetic to the actual digits

Three source identities close the application proof:

1. For any word over `{0,1}`, `binaryWeight (wordValue 2 word)` equals
   `Blocks.count [1] word`. The proof reverses the most-significant-first word
   for mathlib's `Nat.ofDigits` convention. Leading zeroes are retained in the
   word, and the binary alphabet hypothesis is required.
2. `wordValue 2 (powerDigits 0 N)` satisfies `PrefixCertificate (2^N)`.
   The existing evaluator correctness theorem and `scaledFloor 2 0 = 0`
   identify its value with the exact origin prefix.
3. The existing count bridge identifies the one count in that length-`N`
   word with `occurrences 2 1 1 N`.

`certified_binary_ones_bound` also transfers the result to any supplied finite
word with a proof of `DigitsAt 2 0 word`. The start `0` is part of the theorem.
An arbitrary shifted segment need not satisfy this prefix bound.

## Shared dependency and mechanical acceptance

The reusable arithmetic source lives upstream in
`larsbx/finite-math-kernels`, in `tests/lean/FiniteMathKernels/BinaryWeight.lean`.
It is imported through a separate exact Git dependency in `lakefile.toml` and
`lake-manifest.json`, with source root `tests/lean`. The native BigZ submodule
keeps its existing revision; no executable kernel or native fixture changes
are part of this milestone.

The full downstream gate checks that the two dependency declarations agree,
checks the upstream checkout revision and cleanliness, and compares the proof
file byte-for-byte with its pinned Git blob. It copies those exact bytes into
the evidence directory, compiles them into the run's fresh library, and audits
every compiled declaration in that module alongside every project module.
Source hashes and dependency identities are checked again before acceptance.
An existing cached upstream proof object is not used as the acceptance result.

Seven explicit public contract wrappers retain the certificate, quotient,
alphabet, actual source, and count statements. Positive controls and ten
isolated rejection cases test concrete failure modes:

| Invalid change | Retained counterexample or rejection |
| --- | --- |
| Keep only the lower certificate inequality | `N=3,q=0` fails the bound. |
| Keep only the upper certificate inequality | `N=5,q=32` fails the bound. |
| Count binary length instead of one bits | `8` has weight `1` and digit-list length `4`. |
| Make weight additive across every sum | `1+1` has a carry and weight `1`. |
| Drop the alphabet condition | The word `[2]` has numeral weight `1` and no one symbol. |
| Remove the additive constant | The certified prefix `N=3,q=4` fails `2N<=s^2+3s`. |
| Apply the prefix bound to any shifted segment | The actual digits at positions `7,8,9` are all zero. |
| Require at least half ones at every prefix | The actual first three digits are `[1,0,0]`. |
| Substitute one checked prefix for the universal bound | The independent expected theorem type rejects it. |
| Change the scale to a different base | The independent binary certificate type rejects it. |

The half-frequency example only refutes an assertion about **every finite
prefix**; it says nothing against limiting simple normality. The shifted
segment is bound to the actual power inputs and source positions, rather than
being an arbitrary all-zero word.

The twelve Python source and dependency admission tests also reject mismatched or moving
pins, missing or duplicate dependency entries, dirty sources, wrong source
roots, a clean checkout at the wrong revision, and a changed proof file hidden
from ordinary Git status with `assume-unchanged`. The same byte comparison binds
every application source input to its reported clean source commit, at both
admission and completion. The input inventory must match the committed source
file set; omitted inputs and dirty checkouts cannot record acceptance.

Run the complete procedure from the repository README. The accepted report
records the exact source commit, dependency revision and proof hash, commands,
compiled types, transitive assumptions, positive and negative controls, and
the inherited native and finite-certificate checks. This document states the
contracts; a report for the exact revision supplies execution evidence.

## Relation to the literature

Bailey, Borwein, Crandall, and Pomerance,
[*On the binary expansions of algebraic numbers*](https://www.davidhbailey.com/dhbpapers/algebraic-bits.pdf),
give binary-weight carry estimates in Lemma 4.1 and Theorem 4.2. The polynomial
truncation argument in Theorem 5.2 compares a long high-bit block with a weight
upper bound; the paragraph following Corollary 5.3 explicitly specializes their
eventual square-root bound to `(sqrt(5)-1)/2`.

The present proof specializes that method to the existing exact prefix
certificate and supplies an explicit bound valid at every `N`, using the
triangular square estimate proved upstream. The paper is mathematical context,
not an imported Lean assumption. This is a formalization and source-transfer
milestone, with no claim of priority or normality.
