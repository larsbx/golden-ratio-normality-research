# Normality from sparse prefix checkpoints

This milestone proves that the full normality target is equivalent to its
restriction to square numbers of starting positions. It first proves a
general endpoint criterion for strictly increasing checkpoint sequences with
vanishing relative gaps, then discharges that geometric condition for squares.
The remaining hypothesis is the eventual block-frequency estimate for the
actual golden-ratio digits at those checkpoints.

## 1. What is sampled

For a base b, width k, and block value j, write

\[
D_{b,k,j}(N)=\left|b^k\operatorname{occurrences}(b,k,j,N)-N\right|.
\]

The count considers every one of the first N starting positions. At the
checkpoint N=i^2, a width-k count therefore uses the first i^2+k-1 digits.
The digits between checkpoints remain part of the prefix. This is not the
sequence obtained by keeping only digits at square positions, and the binary
automaton inputs remain 2^n for consecutive n.

The new [SparseCheckpoints.lean](../GoldenNormality/SparseCheckpoints.lean)
defines `NormalOnCheckpoints b q` by the exact integer statement

\[
b\ge2\quad\land\quad
\forall k\ge1\ \forall j<b^k\ \forall T\ge1\
\exists i_0\ \forall i\ge i_0,
\qquad D_{b,k,j}(q(i))T\le q(i).
\]

The checkpoint sequence q is fixed before these quantifiers. The eventual
index may depend on k, j, and T. No condition on the growth of q is hidden
inside this definition.

## 2. Separate endpoint and gap budgets

The previously accepted interpolation theorem gives, whenever L<=N<=R,

\[
D(N)\le \max(D(L),D(R))+(R-L).
\]

The new exact arithmetic lemma allows its combined budget to be supplied as
three independent inequalities. For T>=1, assume

\[
4T D(L)\le L,\qquad
4T D(R)\le R,\qquad
4T(R-L)\le L.
\]

Then Lean proves

\[
T\bigl(\max(D(L),D(R))+(R-L)\bigr)\le L,
\]

and consequently D(N)T<=N throughout the closed interval.

The different endpoint denominators matter. The gap bound implies R<=2L.
Thus 4T times the larger endpoint error is at most 2L, and T times the gap
is at most L/4. Their sum is at most 3L/4, hence at most L. The implementation
proves the integer inequality directly, including L=0, without division or
floating point arithmetic. The constants are sufficient bounds, with no
optimality claim.

The public lemmas are `checkpoint_budget_of_endpoint_bounds` and
`occurrences_interval_bound_of_endpoint_bounds`. The second retains one base,
width, value, and source interval throughout.

## 3. An endpoint-only equivalence

`VanishingRelativeGaps q` means

\[
\forall T\ge1\ \exists i_0\ \forall i\ge i_0,
\qquad (q(i+1)-q(i))T\le q(i).
\]

With `StrictMono q` as a separate hypothesis, Lean proves

```lean
normalInBase_iff_normalOnCheckpoints (b : Nat)
    (hq : StrictMono q) (hgaps : VanishingRelativeGaps q) :
  NormalInBase b <-> NormalOnCheckpoints b q
```

The forward direction needs only strict increase: every strictly increasing
natural sequence has q(i)>=i, so a full eventual bound also holds at its late
checkpoints.

For the reverse direction, fix k, j, and T. Obtain the endpoint estimate at
tolerance 4T and the gap estimate at tolerance 4T, and take the larger of
their two starting indices. Both endpoints of every later interval now satisfy
the finite lemma. Strict increase makes those consecutive intervals cover
every sufficiently large N. The existing checkpoint coverage theorem supplies
the interval containing N and the positive threshold required by NormalInBase.

These are infinite hypotheses. A finite list of checkpoint certificates does
not provide either eventual statement. A constant zero sequence makes both
endpoint and gap predicates vacuous; the separate strict-increase hypothesis
prevents its use in the equivalence.

## 4. Squares discharge the geometric obligation

[SquareCheckpoints.lean](../GoldenNormality/SquareCheckpoints.lean) defines
`squareCheckpoint i := i^2` and proves strict increase and the exact gap

\[
(i+1)^2-i^2=2i+1.
\]

For every T>=1, the explicit threshold i>=3T gives

\[
(2i+1)T\le i^2.
\]

Indeed, i^2>=3iT and (2i+1)T<=3iT for i>=1. This proves the complete
vanishing-relative-gap predicate for squares. The resulting theorem is

```lean
normalInBase_iff_squareCheckpoints (b : Nat) :
  NormalInBase b <-> NormalOnCheckpoints b squareCheckpoint
```

The finite specialization `occurrences_square_interval_bound` is also public:
if i>=12T and the two endpoint discrepancies at i^2 and (i+1)^2 meet
tolerance 4T, every N in between meets tolerance T. The threshold 12T applies
the geometric lemma with 4T. It is a threshold for the gap estimate, not a
threshold at which the golden-ratio endpoint estimates become true.

## 5. The computable binary target

Inside `GoldenNormality.BinaryAutomaton`, `PowerOrbitSquareNormality` states

\[
\forall w\ne[]\text{ over }\{0,1\}\ \forall T\ge1\
\exists i_0\ge1\ \forall i\ge i_0,
\]

\[
\left|2^{|w|}\operatorname{Blocks.count}
  \bigl(w,\operatorname{powerDigits}(0,i^2+|w|-1)\bigr)-i^2\right|T\le i^2.
\]

The exact count bridge and fixed-width word coverage prove

```lean
powerOrbitSquareNormality_iff_normalInBase :
  PowerOrbitSquareNormality <-> NormalInBase 2
```

Every word, tolerance, positive eventual index threshold, and later index is
retained. In particular, an endpoint condition at one index, at a finite list
of indices, or for a single block is not the proposition in this equivalence.
The computable count has origin zero and contains i^2 complete starts.

## 6. Controls and literature boundary

The compiled controls check the explicit square threshold, the constant-zero
vacuity, the failure of the relative-gap condition for q(i)=2^i, and weakened
theorem types. A short binary prefix checks that a square number of starts
still needs the final k-1 digits. Each semantic rejection runs separately and
must fail with its intended diagnostic.

An abstract single-count family illustrates why endpoint interpolation needs
a gap restriction. For M>=1, set

\[
C_M(N)=\lfloor\min(N,2M)/2\rfloor+\min(N-2M,M),
\]

where subtraction is truncated in the naturals. This is a monotone count with
increments at most one. At 2M and 4M its binary scaled discrepancy is zero;
at 3M that discrepancy is M, which violates tolerance 4. The controls prove
these statements for every positive M. This concerns one abstract count over
one interval at each scale. It is not an assertion about the golden-ratio
digits or a counterexample to an all-block normality criterion.

The proportional primary-source check revisited Kozachinskiy and Shen,
[*Automatic Kolmogorov complexity, normality, and finite state dimension
revisited*](https://arxiv.org/html/1701.09060v6), section 4.2. Their presentation
of the Piatetski-Shapiro criterion states that one common constant bounding
every block's upper frequency by that constant times its uniform frequency
suffices for normality. Consequently, failure of the gap hypothesis for a
geometric sequence must not be presented as failure of every possible
all-block checkpoint argument. The current proof uses elementary interpolation;
it neither formalizes nor assumes that stronger published criterion. The
relative-gap condition is sufficient for the route proved here, with no
necessity claim for all normality criteria.

## 7. Acceptance and remaining obligation

Seven explicit public contract wrappers preserve the full new theorem types.
The gate builds both new project modules and the generated counterexample
module, inspects their compiled declarations and transitive assumptions, and
retains every inherited native fixture, receipt, exact-type check, and rejection
control. No native producer or dependency pin changes in this milestone.

After installing the pinned dependencies, use a fresh output directory:

```sh
python3 tools/verify.py --output build/sparse-checkpoint-acceptance
```

The exact source revision and observed acceptance belong in the resulting
report and its evidence packet. Hosted acceptance is recorded separately.

The remaining research obligation is to establish the displayed endpoint
frequency condition for the golden-ratio power orbit at every sufficiently
late square checkpoint, for every nonempty binary word and every positive
tolerance. The new geometry and equivalences provide no such distribution
estimate and establish no unconditional normality result in any base.
