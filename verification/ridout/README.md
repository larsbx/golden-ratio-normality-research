# Ridout replay and golden-ratio specialization

This isolated package uses Lean 4.35.0-rc3 and Subspace-Theorems commit
2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d. The root application keeps its existing
Lean 4.34.0-rc2 toolchain. The GoldenNormality modules are compiled directly from
the same checkout through srcDir = "../.."; no contract or carry theorem is copied.

**Local proof acceptance passed** at source revision
`2ba20e1ceee5b3a270e501983faccf4edfe92384`. The
[exact-source evidence](../../evidence/ridout/2ba20e1c/README.md) includes the
compiled theorem types, transitive axiom audit, and replay receipt. Hosted CI
has a separate status.

## The proof

Let $\alpha=(\sqrt5-1)/2=\varphi-1$ and let
$z_N=\operatorname{occurrences}(2,1,0,N)$ be the number of zeros among its
first $N$ binary digits, indexed from zero after the radix point.

### Exact input and finite exceptional set

For a real $\xi$ with $0<\xi<1$, the two mathematical hypotheses are
`IsAlgebraic ℚ ξ` and `Irrational ξ`. For each positive integer $B$, define

$$
X_B=\left\{r\in\mathbb Q:\ 0\le r\le1,\quad
q\mid2^m\text{ for some }m,\quad
|\xi-r|^Bq^{B+1}\le1\right\},
$$

where $q$ is the positive reduced denominator of $r$. The theorem
`finite_dyadicCandidates` proves that $X_B$ is finite, using the actual
`Rat.finite_setOf_ridout` with no numerator primes, denominator primes
`Nat.primesOf 2`, and $\varepsilon=1/B$.

This specialization keeps Ridout's reduced height. On $[0,1]$,
$\max(|\operatorname{num}(r)|,q)=q$. Since $q\mid2^m$, all its prime factors
are two, so `Rat.prod_padicNorm_natCast` gives the exact local factor $1/q$.
The powered condition yields

$$
|\xi-r|\le q^{-1-1/B},\qquad
|\xi-r|\,|q|_2\le q^{-2-1/B},
$$

which is precisely the required Ridout inequality. The proof uses the reduced
denominator even when the original numerator is even.

### From finite rationals to all integer numerators

The theorem `eventualDyadicSeparation_of_finite_candidates` proves

$$
\forall B\ge1\;\exists M_B\;\forall m\ge M_B\;\forall p\in\mathbb Z,
\qquad |2^m\xi-p|^B2^m\ge1.
$$

To check this step independently, suppose the bound fails at arbitrarily large
$m$. Put $Q=2^m$ and $r=p/Q$. A failure gives

$$
|\xi-r|^BQ^{B+1}<1.
$$

The reduced denominator $q$ divides $Q$, so replacing $Q$ by $q$ preserves the
upper bound. Also $|Q\xi-p|\le1$, hence $|\xi-r|\le2^{-m}$. For sufficiently
large $m$, this puts $r$ in $[0,1]$ and in $X_B$, with error arbitrarily close
to zero. Every element of the finite set $X_B$ has positive distance from the
irrational $\xi$; its minimum distance is therefore positive, a contradiction.
This argument covers repeated representations of the same rational.

### Golden-ratio specialization and count consequences

`algebraic_alpha` uses the nonzero polynomial $X^2+X-1$ and the existing exact
quadratic identity. The existing `BinaryDyadicOrbit.irrational_alpha` supplies
irrationality. `alpha_eventualDyadicSeparation` then proves the exact existing
`BinaryComplement.EventualDyadicSeparation` definition, including all integer
numerators and its original order of quantifiers.

The existing carry transfer gives these two endpoint statements:

| Theorem | Exact hypotheses and conclusion |
|---|---|
| `zero_count_eventually_exceeds` | For every real $c\ge0$ with $c^2<2$, there is $M$ such that every $N\ge M$ satisfies $z_N>c\sqrt N$. |
| `zero_count_exceeds` | For every real $c\ge0$ with $\pi c^2<8$ and every natural $M$, there is $N\ge M$ with $z_N>c\sqrt N$. |

These imply, mathematically, $\liminf z_N/\sqrt N\ge\sqrt2$ and
$\limsup z_N/\sqrt N\ge\sqrt{8/\pi}$. The Lean endpoints retain the quantified
inequalities in the table, rather than defining a new liminf/limsup interface.
Ridout supplies no computable cutoff here. These square-root-scale lower bounds
do not give frequency $1/2$, positive lower density, block normality, or
cancellation of the actual binary orbit.

## Repetitions at a fixed lag

For a fixed nonzero integer $h$, apply the dyadic specialization to the
fractional part of $h\alpha$. Irrationality survives integer multiplication by
$h$ and subtraction of the floor. Both operations also preserve algebraicity.
The floor term contributes an integer after multiplication by $2^n$, so for
each integer $B\ge1$ there is a threshold $M(h,B)$ such that

$$
1\le 2^n |2^n h\alpha-p|^B\qquad(n\ge M(h,B),\ p\in\mathbb Z).
$$

At a fixed lag $d>0$, set $h=2^d-1$. The difference $x_{n+d}-x_n$ of the
actual orbit points $x_n=\{2^n\alpha\}$ differs from $2^nh\alpha$ by an
integer. If the width-$k$ blocks at these starts agree, both points occupy
the same half-open dyadic cell, so their distance is strictly below $2^{-k}$.
Combining these inequalities yields $Bk<n$ at every sufficiently late start,
uniformly in the tested width $k$. Consequently the longest repeated width
at each fixed lag is $o(n)$. The threshold depends on the lag and $B$.

The same estimate applies to the frequencies $(2^d-1)h$ in the
[lag criterion](../../docs/binary-dyadic-orbit.md#one-sided-control-on-spaced-lags).
It bounds the rate at which individual phases can approach $1$. To see why
this leaves the average open, consider the irrational source
$\xi=\sum_{j\ge1}2^{-j^2}$. Its binary expansion has infinitely many ones and
unbounded zero gaps. For $(j-1)^2\le n<j^2$, put $r=j^2-n$. Then
$\{2^n\xi\}=2^{-r}(1+\delta_j)$ with $0<\delta_j\le2^{-2j}$ by a geometric
tail bound. For fixed odd $h$, the distance of $h2^{-r}$ to the nearest integer
is at least $2^{-r}$. The perturbation is at most $2^{-r-1}$ for all large
$j$. Since $r\le2j-1$ and $n\ge(j-1)^2$, this proves the same eventual
separation for every fixed $h,B$. An even multiplier reduces to its odd part
after a fixed shift, which changes the exponent by a fixed additive constant.
Within each interval of starts the sum of $\{2^n\xi\}$ is less than $2$.
Thus for every fixed frequency the sum of distances of its phases from $1$
is $O_h(\sqrt N)$, and the average tends to $1$. This is a written control
on what fixed-multiplier separation can imply about averages.

## Replay and acceptance

Run from this directory:

    python3 replay.py

The replay verifies every locked dependency revision, binds all imported source
and audit/configuration bytes to their owning repository's exact Git blobs,
obtains the required Mathlib cache roots, builds the selected proof closure,
and records source hashes and a compiled axiom audit under build/. It repeats
the source, configuration, and HEAD checks before accepting the result.
The audit fixes the full Ridout type and the exact dyadic and zero-count types,
and permits only propext, Classical.choice, and Quot.sound. A rational 1/2 control
shows why algebraicity alone cannot imply the all-numerator separation statement;
the actual alpha at m=0 shows that the eventual threshold cannot be deleted.

The claim ledger assigns the dyadic separation, fixed-lag, and unconditional
count declarations to the `ridout` acceptance lane. The replay
binds their exact ledger entries, audit, workflow, compiled application source,
and dependency lock to the checked-out Git revision. The compiled audit fixes
the declared quantifiers and checks both count inequalities at `c = 1`.
The two separation controls check the rational `1/2` and the actual exponent
zero case. The lag controls exercise a negative multiplier, lag zero, and the
actual overlapping repeat at starts 10 and 14 that requires a cutoff. All
thirteen audited declarations must appear in the transitive axiom log.

The output directory must be new. To repeat a replay, pass a fresh ignored path
such as `--output build/repeat`. A missing toolchain, failed build, absent audit
marker, changed dependency, or changed source is a failure. This package does not invoke all upstream default
libraries: unrelated paper targets at this pin include an absent NairKumarRout2025
directory.

This is a proof-only acceptance lane. It is separate from the root project's full
native Mojo/Python acceptance. A successful isolated replay does not migrate the
root toolchain or make this dependency available to the root default build.

Hosted replay installs the official Lean release archive directly and checks
SHA-256 `1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997`.
The expected Lean binary reports compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`.

From this directory, verify a fresh local receipt against its exact commit:

```sh
python3 claim_evidence.py "$(git rev-parse HEAD)" --local build
```

For hosted acceptance, use GitHub CLI with Actions read access and the run ID of
**Ridout proof replay** for that exact commit:

```sh
python3 claim_evidence.py "$(git rev-parse HEAD)" --run-id "$ridout_run_id"
```

The hosted check fetches the run and job from GitHub, verifies the replay and
upload steps of the successful attempt, downloads its exact-head artifact,
checks GitHub's archive digest, and verifies the receipt and audit. If a path
filter skipped the run, dispatch the workflow on a ref pointing to that commit
before recording hosted acceptance. Check the separate Foundation acceptance
run for the integration revision as well. Historical receipts predate this
registration and remain evidence only for their recorded revisions and checks.

## Provenance

The application is stacked on PR #32 at
a680e02f70e68f50194ee981e7d8d7701e3833a5. The imported theorem is Ridout's classical
theorem, formalized in rwst/Subspace-Theorems; this adapter claims no new classical
normality theorem. External source remains in its pinned Apache-2.0 dependency.
