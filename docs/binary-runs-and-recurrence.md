# Binary runs and quantitative recurrence

For the actual fractional binary digits of `alpha = phi - 1`, a constant run
beginning at zero-based position `n` has length at most `n+1`. Consequently,
every segment at positions

\[
\boxed{n\le i<2n+2}
\]

contains both zero and one. The right endpoint is exclusive. The result applies
at every natural `n`, including zero, without a normality hypothesis.

The same theorem concerns the total computable `powerDigits` sequence and any
supplied word with a proved `DigitsAt 2 n` binding. The original start position
is part of the bound: a shifted word cannot be presented as an origin prefix.

## Quantitative count consequence

Let `c_d(N) = occurrences 2 1 d N`, for `d < 2`. Define

\[
a_m=2^{m+1}-2.
\]

Then `a_0=0` and `a_(m+1)=2*a_m+2`. The disjoint windows
`[a_m,a_(m+1))` each contain both symbols. Induction gives

\[
\boxed{c_d(2^{m+1}-2)\ge m}\qquad(d\in\{0,1\}).
\]

By monotonicity the same lower bound holds at every `N >= 2^(m+1)-2`.
This is an explicit logarithmic growth guarantee for **each** symbol, and it
rules out every eventually constant tail. It is weaker than the separately
proved square-root-scale bound for ones. Neither estimate establishes positive
limiting density, limiting frequency one half, or an all-block frequency bound.

## Exact endpoint argument

Put `B=2^n`, `D=2^k`, and let `q` and `Q` be the certified prefix numerals at
positions `n` and `n+k`. Their certificates say

\[
q^2+Bq\le B^2<(q+1)^2+B(q+1),
\]

and the same inequalities at scale `BD` for `Q`. Both certificates are required.
They also give `q<B` and `Q<BD`. The existing modulo-three obstruction makes
the first lower inequality strict, so its positive integer residual is at
least one.

**Zero run.** If the intervening `k` digits are all zero, `Q=Dq`. The lower
residual at the second endpoint is

\[
(BD)^2-Q^2-BDQ=D^2(B^2-q^2-Bq)\ge D^2.
\]

The upper half of the second certificate bounds this residual strictly below
`2Q+BD+1`, which is at most `3BD-1`. Thus `D^2<3BD`.

**One run.** If those digits are all one, `Q+1=D(q+1)`. The upper residual is

\[
(Q+1)^2+BD(Q+1)-(BD)^2
 =D^2((q+1)^2+B(q+1)-B^2)\ge D^2.
\]

The lower half of the second certificate bounds this residual by
`2Q+BD+1`, again strictly below `3BD`. Hence `D^2<3BD` here too.

In either case, a run with `k >= n+2` would have `D >= 4B`, contradicting the
residual bound. This proves `k <= n+1`. The formal proof works with exact
natural-number inequalities; no floating-point approximation, statistical
sample, or unproved irrationality measure enters it.

The source transfer uses the certified origin-prefix numerals, the exact
positional value of the intervening word, and its retained start and length.
The recurrence proof then composes disjoint segments and uses singleton
counts, so no chunk-boundary correction or overlapping-start loss is hidden.

## Counterexamples and acceptance

The following actual digit segments make two tempting stronger variants false:

| Source-bound segment | What it excludes |
| --- | --- |
| Positions 1 and 2 are `[0,0]`. | A universal run bound `k <= n`, or a guarantee that every length-`n+1` window contains one. |
| Positions 3 through 6 are `[1,1,1,1]`. | The corresponding stronger claim for one runs or zero recurrence. |

These examples show that reducing the additive constant uniformly is invalid;
they do not assert that the bound is attained at every start. Their source
identities are proved from exact root certificates. Arbitrary constant words,
nonbinary symbols, missing endpoint certificates, shifted sources, shortened
windows, and changed recurrence thresholds are covered by isolated rejection
controls and explicit public theorem-type checks.

Run the full acceptance command in the README. It fresh-compiles the new
modules, checks their public types, audits all transitive assumptions, and
replays the inherited native and finite-certificate gates. This is a proof
increment; it does not establish universal refinement of the Mojo producers,
BigZ, or their compiler. Exact source acceptance is recorded by the report,
not by the presence of this document.

## Literature and next obligation

Bailey, Borwein, Crandall, and Pomerance,
[*On the binary expansions of algebraic numbers*](https://www.davidhbailey.com/dhbpapers/algebraic-bits.pdf),
Section 3, relate digit gaps to eventual logarithmic growth using Roth's
theorem. The result here is an elementary, explicit specialization for this
quadratic, with all starts included; no priority claim or imported Roth
assumption is made.

The complementary number `beta=1-alpha` satisfies `beta^2-3*beta+1=0`.
Its negative linear coefficient prevents direct reuse of the positive
polynomial argument underlying the current one-count bound. The paper's
general Theorem 7.1 already gives stronger eventual square-root growth for
this algebraic complement, but that theorem is **not formalized here**.
The [subsequent complement and carry development](binary-complement-and-carries.md)
now proves the source-bound complement identities and finite signed carry
groundwork. Its aggregate counting step remains open. The present explicit
gap bound is a prerequisite for that route. Normality still requires the separate all-block
eventual estimates, for example at the proved square checkpoints.
