# Dyadic orbit and the binary normality obligation

Let \(\alpha=\varphi-1\) and \(x_n=\{2^n\alpha\}\). The actual block
with width \(k\) and start \(n\) is \(\lfloor2^k x_n\rfloor\), including
leading zeros. Lean checks that the block has value \(j\) exactly when
\(x_n\in[j/2^k,(j+1)/2^k)\). Counting these visits at starts
\(0,\ldots,N-1\) gives the repository's exact occurrence count.
The checked equivalence retains every positive width, valid cell, tolerance,
and eventual threshold from `NormalInBase 2`.

## Fourier reduction

Write \(u_h(n)=\exp(2\pi i h 2^n\alpha)\) and
\(A_h(N)=N^{-1}\sum_{n<N}u_h(n)\).
Lean checks the equality with the phase evaluated at \(x_n\), the identities

\[
u_h(n+d)=u_{2^d h}(n),\qquad
u_h(n+d)u_{-h}(n)=u_{(2^d-1)h}(n),
\]

and the boundary estimate

\[
|A_{2h}(N)-A_h(N)|\le 2/N\qquad(N>0).
\]

Lean proves `normalInBase_of_odd_mode_cancellation`: if
\(A_h(N)	o0\) for every odd integer \(h\), then `NormalInBase 2`.
The proof first transfers cancellation to every nonzero mode.
The empirical probability measure places equal mass on the first
\(N+1\) starts. Its integrals converge on the Fourier monomials,
and their linear span is dense among continuous functions on the
circle. Integration against each probability measure is
1-Lipschitz in the uniform norm, so convergence extends to every
continuous function. The portmanteau theorem then gives convergence
of the mass of each half-open dyadic cell: its boundary lies in
the two endpoints, both of Haar measure zero. The proof identifies
that mass with the exact finite count, and recovers the repository's
integer discrepancy inequality for each positive tolerance denominator.

The argument formalizes the sufficient direction of the classical
[Weyl criterion](https://citeseerx.ist.psu.edu/document?doi=8f963e72562eaa43a7c85ac65f8b24af7ac47501&repid=rep1&type=pdf)
using mathlib's Fourier density and portmanteau theorems.

The lag identity supplies no decay by itself. In particular, lag one
returns the original mode rather than a mode with an independently known
bound. At larger fixed lags the multiplier remains odd. The cancellation
of the actual orbit at these frequencies is the unresolved estimate.

## Checked limitation of scalar bounds

The alternating sequence beginning with one has zero count
\(\lfloor N/2\rfloor\). Lean proves that it satisfies
\(N\le z_N^2+7z_N\) for every \(N\ge2\), eventually exceeds
\(C\sqrt N\) for every fixed \(C\ge0\), and has no occurrence of
\(00\) at any start. This control addresses implications from the
scalar count consequences. It makes no claim that the alternating sequence
satisfies the source-specific signed carry identities.

Run `python3 tools/verify.py --output build/replay-dyadic-orbit` for the
pinned replay. The binary normality target remains open.

## Exact quadratic-norm return bound

For integers \(p,q\) with \(q\ne0\), write \(e=q\alpha-p\). The actual
quadratic equation gives

\[
e(e-\sqrt5\,q)=p^2+pq-q^2.
\]

Both factors are nonzero by irrationality, so the absolute value of the
integer on the right is at least one. The triangle inequality yields
\(1\le |e|(|e|+\sqrt5\,|q|)\). Taking
\(q=2^m-2^n\) and
\(p=\lfloor2^m\alpha\rfloor-\lfloor2^n\alpha\rfloor\) gives, for \(n<m\),

\[
1\le |x_m-x_n|\bigl(|x_m-x_n|+\sqrt5(2^m-2^n)\bigr).
\]

If a width-\(k\) block is repeated at those two starts, both orbit points
are in the same half-open cell and \(|x_m-x_n|<2^{-k}\). Thus

\[
2^k<1+\sqrt5(2^m-2^n),\qquad k\le m+1.
\]

The starts may overlap. In particular the actual nonconstant word
\(110111\) occurs at both starts 10 and 14, so the width can exceed
the distance between starts. Lean checks these occurrences from the
four exact prefix certificates. An independent integer-square-root
oracle replays this witness and checks the width bound for the longest
shared block visible at every pair of starts in a 192-digit prefix.
Run `python3 -m unittest discover -s tests -p test_dyadic_separation.py`
to reproduce those finite controls.

The separation scale decreases exponentially in the later start, so
the inequality places no upper density bound on repeated visits to a
fixed-width cell. In the more general setting, a uniform rational
approximation lower bound of order \(q^{-2}\) is compatible with a
nondense doubling orbit. The badly approximable reals and
the reals whose doubling orbit avoids a neighborhood of zero are
both winning sets for Schmidt's game, and their intersection is
winning. This is a literature-based obstruction to using bad
approximability alone. It does not concern the specific algebraic
number \(\alpha\). See [Schmidt, *On badly approximable numbers and
certain games*](https://doi.org/10.2307/1994619) and [Broderick,
Fishman, and Kleinbock, Theorem 1.2 and Section 5](https://people.brandeis.edu/~kleinboc/Pub/bfkDec8.pdf).

## A finite cutoff in frequency can miss a larger odd mode

For every cutoff \(H\), choose \(k\) with \(3^k>H\) and use the
rational source \(x=1/3^{k+1}\). The period of \(2^n\) modulo
\(3^{k+1}\) has length \(2\cdot3^k\) and visits each unit once.
The complete-period phase sum is the sum over all residues minus
the sum over the multiples of three. For \(0<|h|\le H\), these are
complete nontrivial character sums modulo \(3^{k+1}\) and \(3^k\),
so both vanish. An incomplete last period contributes at most
\(2\cdot3^k\) in magnitude, and the averages tend to zero. At the
odd frequency \(h=3^{k+1}\), every phase is one.

Lean checks this construction for every cutoff in
`finite_modes_can_miss_larger_odd`. The rational source supplies a
control for general doubling-orbit arguments. The golden-ratio
source and its conditional cancellation statement are the same
as in the preceding sections.

## Exact finite modular sums for the actual source

Let $Q_N=\lfloor2^N\alpha\rfloor$ and $q_N=2^N$. Lean proves that
replacing the source by its certified truncation $Q_N/q_N$ changes
the normalized Fourier average over the first $N$ starts by at most
$2\pi|h|/N$. For $N>0$, this follows from the bound on phase
distance, $|\alpha-Q_N/q_N|<1/q_N$, and
$\sum_{n<N}2^n=q_N-1$.

The resulting average is exactly `dyadicModularAverage h N`.
Its phases are $q_N$-th roots of unity with exponents
$hQ_N2^n\bmod q_N$. For each fixed $h$, this exact modular average
tends to zero if and only if the actual average tends to zero.
Lean checks both directions of the equivalence
`normalInBase_iff_dyadic_modular_cancellation`.
For the converse, group the actual phases by their width-$k$ dyadic cell
and replace each phase by its value at the left endpoint. The normalized
error is bounded by $2\pi|h|/2^k$, uniformly in the number of starts.
Normality gives the limiting weights of all the cells at that fixed
width. For $2^k>|h|>0$, the sum of their left-endpoint phases vanishes
by additive-character orthogonality. Letting the approximation error
shrink gives decay at the original fixed mode. The needed estimate
is that the sum of these roots of unity has magnitude $o(N)$
as $N$ grows, with $Q_N$ the actual quadratic floor.

## Complete-frequency second moments

For any list of $N$ residue positions modulo $q$, Lean proves that
the sum of the squared phase-sum magnitudes over all $q$ frequencies
is $q$ times the number of ordered pairs of equal residues. This is
finite additive-character orthogonality. For $q=2^N$ and an odd
numerator, the $N$ residues of the doubled orbit are distinct.
The second moment is exactly $2^N N$, including at each actual
odd quadratic floor.

The invariance is stronger than equality of one moment. Multiplication
by an odd numerator permutes the frequency labels, so averaging any
real function of the complex phase sums over the full frequency set
has the same result as for numerator one. In the family of rational
seeds $1/2^N$, the normalized sum at the fixed frequency $1$ tends to
one. Lean proves this using the same perturbation bound at the zero
source. Thus complete-frequency averages alone cannot give the
required fixed-frequency decay. The control uses a varying rational
seed at each $N$, as in the finite modular problem.

## Exact nonvanishing at finite lengths

For any numerator $p$ modulo $2^N$, put
$\zeta=\exp(2\pi i p/2^N)$. Lean proves that
$\sum_{0\le n<N}\zeta^{2^n}$ is nonzero for every $N\ge3$.
The order of $\zeta$ divides $2^N$, so it is $2^M$ for some $M\le N$.
The order-one and order-two cases give sums $N$ and $N-2$.
For $M\ge2$, the last $N-M$ terms equal one and the term at $n=M-1$
equals minus one. The remaining expression evaluates a rational polynomial
whose coefficient of $X$ is one and whose degree is less than $2^{M-1}$.
The minimal polynomial of $\zeta$ has degree $2^{M-1}$, so it cannot divide
that polynomial. This proves `dyadicModularAverage_ne_zero` for the actual
quadratic floor at every integer frequency, including zero.

The threshold is sharp. At $N=2$ the actual prefix numerator is two, so
every odd frequency has phases $-1,1$. Lean checks the frequency-one
case. The Python control independently reduces the phase polynomial
modulo $X^{2^{N-1}}+1$, checks all 2,040 residues across lengths 3 through
10, and replays the actual length-two exception with positive and
negative odd frequencies. Run
`python3 -m unittest discover -s tests -p test_dyadic_modular.py`.

The exact nonvanishing statement is compatible with convergence of the
normalized averages to zero. It also holds for the varying rational
seeds above, whose averages at frequency one converge to one. The
normality criterion still requires $o(N)$ at each fixed odd frequency
for the actual quadratic floors.

## Ordered frequency-one deficit

Let $S_N=N\,\texttt{dyadicModularAverage}(1,N)$ and let $T_N$ count
changes between adjacent digits among the first $N$ bits. The phase at
start $j$ is that of the zero-padded suffix of the exact $N$-bit prefix.
For $j<N-1$, a change means the first two bits of that suffix are
`01` or `10`, putting the phase $z_j$ in the closed left half-circle.
The next phase is $z_j^2$, so $|z_j+z_j^2|^2=2+2\operatorname{Re}z_j\le2$
at every transition. The adjacent pairs cover each interior phase twice.
Including both endpoints gives
`norm_dyadicModularAverage_one_mul_add_transition_le` in Lean,
with no approximation of the modular phases:

$$
|S_N|+(1-1/\sqrt2)T_N\le N.
$$

The window between digit indices $2^j-1$ and $2^{j+1}-1$ contains both
symbols by the quadratic constant-run theorem. Consecutive windows share a
digit but no adjacent pair. Thus $T_N\ge k$ whenever $2^k\le N$.
Lean checks this source-specific consequence in
`norm_dyadicModularAverage_one_mul_add_log_le`. Applying
[Bugeaud and Evertse, Theorem 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/83574)
with base two and degree two gives the additional literature-based bound
$N-|S_N|\gg(\log N)^{3/2}/\sqrt{\log\log N}$ for sufficiently large $N$.

For any binary prefix, if $r$ equal bits remain in a run, the phase is within
$2\pi\,2^{-r}$ of $1$. Summing within runs gives the reverse estimate
$|N-S_N|\le2\pi(T_N+1)$. The alternating rational control with source
$1/3$ has a limiting first-mode average of $-1/2$ despite a transition
at every pair. The infinite word $0^1 1^1 0^2 1^2\cdots$ has balanced
limiting symbol frequencies and satisfies the same individual run-length
bound. Its $O(\sqrt N)$ transitions force $S_N/N\to1$. These controls
measure the reach of run and transition information on its own.

## Quadratic residual and the fixed mode

Put $q_n=2^n$, $a_n=\lfloor q_n\alpha\rfloor$,
$R_n=q_n^2-a_n^2-q_na_n$, and $x_n=q_n\alpha-a_n$.
Lean verifies the next-digit rule and residual step with $d_n\in\{0,1\}$:

$$
a_{n+1}=2a_n+d_n,\qquad
d_n=\mathbf1_{4R_n\ge 2(2a_n+q_n)+1},\qquad
R_{n+1}=4R_n-d_n\big(2(2a_n+q_n)+1\big).
$$

Appending the digit changes the sum by
$(-1)^{d_N}+\sum_{j<N}z_j(e(d_N2^{j-N-1})-1)$, where
$e(t)=\exp(2\pi i t)$. An appended zero gives an increment of exactly one.
For an actual appended one at $N=5$, integer half-angle enclosures give
$0.361<\operatorname{Re}(S_6-S_5)<0.362$. They also give
$24<|S_{20}|^2<25$, refuting the unit-constant $\sqrt N$ estimate.

The exact factorization $R_n=x_n(2a_n+q_n+x_n)$ gives the rational proxy
$y_n=R_n/(2a_n+q_n)$ with $0\le y_n-x_n\le2^{-n}$.
The pointwise errors are summable. Lean checks
`norm_dyadicModularAverage_sub_residualProxyAverage_le`, which bounds the
difference between the modular average and the average of $e(hy_n)$ by
$6\pi|h|/N$ for every integer frequency $h$ and $N>0$.

For a conditional frequency-one estimate, define

$$
D_{d,N}=\sum_{j<N-d} e(y_{j+d}-y_j),\qquad
E_{H,N}=\frac1H+
  \frac2H\sum_{1\le d<H}\left(1-\frac dH\right)
      \frac{\operatorname{Re}D_{d,N}}{N}.
$$

The sum of the first $N$ pointwise phase errors between the modular and
rational sequences is at most $6\pi$, so each trimmed lag correlation
differs by at most $12\pi$. For the modular sequence, the sum of all
length-$H$ window sums after zero padding is $H S_N$. Expanding the sum
of squared window norms counts every lag-$d$ product $H-d$ times.
Cauchy–Schwarz over the $N+H-1$ windows yields, for $1\le H\le N$,

$$
\frac{|S_N|^2}{N^2}\le
\left(1+\frac{H-1}{N}\right)\left(E_{H,N}+\frac{12\pi}{N}\right).
$$

This last bound is a written deduction. Its remaining sufficient
hypothesis is $\inf_{H\ge1}\limsup_{N\to\infty}E_{H,N}=0$
for the actual residual recurrence. Lag $d$ in the modular sum has
frequency $2^d-1$, so lag one returns the target frequency. The
logarithmic deficit leaves frequency-one $o(N)$ growth open. Full
binary normality retains the requirement at every fixed odd frequency.

Run `python3 -m unittest discover -s tests -p test_fixed_frequency.py`
for the integer recurrence, half-angle enclosures and controls.

## One-sided control on spaced lags

Write $A_h(N)=S_N(h)/N$ for the exact dyadic modular average.
Choose an integer spacing $L>0$, a positive number of shifts $H$, and
a prefix width $N>0$. If

$$
\operatorname{Re} A_{(2^{Ld}-1)h}(N)\le\eta
\quad (1\le d<H),\qquad \eta\ge0,
$$

then Lean proves the finite estimate

$$
|A_h(N)|\le
\sqrt{\frac1H+\eta+\frac{2LH}{N}}+\frac{2LH}{N}.
$$

Average the $H$ copies of the phase sequence at starts $0,L,2L,\ldots$.
Shifting by $t$ changes the normalized sum by at most $2t/N$ by endpoint
cancellation. Cauchy–Schwarz over the $N$ starts bounds the squared norm of
the mixed average by the mean of the squared norms of the mixed phases.
In the expanded square the diagonal contributes $1/H$. Each off-diagonal
term is the real part of a shifted frequency $(2^{Ld}-1)h$ at a lag
$d=|i-j|$. Shifting back costs at most $2LH/N$ independently of the
size of the lag frequency. This argument applies directly to the rational
source $a_N/2^N$ at each width, so the finite estimate uses exact
modular phases and its boundary cost depends on shifts. The averaging
argument uses van der Corput differencing with spaced shifts.
[Kuipers and Niederreiter, Chapter 1, Section 3](https://math.rice.edu/~michael/teaching/426_Spr14/Kuipers_Nied_UD.pdf)

For each fixed $h$ and positive $L$, suppose that for each fixed
$d\ge1$ the corresponding real average is eventually at most every
positive tolerance. Select $H$ and the tolerance first, then take $N$
large enough for the finitely many lags and the boundary cost.
`tendsto_dyadicModularAverage_of_lagUpperZero` proves complex
cancellation at $h$. The source-specific bound on the difference
between modular and rational residual averages transfers the one-sided
condition to the residual recurrence at each fixed lag.

Lean proves `normalInBase_iff_sparse_lag_upper` by choosing
$L(h)=2^{|h|}$ independently for every odd $h$. The reverse implication
uses the ordinary normality criterion and the fact that all the tested
modes are nonzero. Negative modes have the same real averages as their
positive conjugates. Among the positive frequencies

$$
\{ h(2^{2^h d}-1) : h\ge1\text{ odd},\ d\ge1\},
$$

at most $\lfloor\log_2(X+1)\rfloor$ lie below or equal to $X$.
Indeed, let $m=\lfloor\log_2(X+1)\rfloor$. For a given $h$ one
has $2^h d\le m$, so the count is bounded by
$\sum_{h\ge1}\lfloor m/2^h\rfloor\le m$. At target frequency
one the schedule starts with $3,15,63,255$.

Exact independent enclosures for the actual $16{,}384$-bit prefix
give real averages below $3/250$ at all $31$ scheduled lags with
$L=2$, $H=32$. The displayed inequality then gives
$|A_1(16384)|<117/500=0.234$. This is a finite certificate.
The rational orbit of $1/9$ has first-mode mean zero over its period,
yet the scheduled mode $63$ has mean one. For $1/3$ the first lag with
$L=1$ has real mean $-1/2$ and the next has mean one. The eventual
one-sided bounds for the actual source remain open.

The isolated Ridout proof gives eventual sublinear repeated-block width for
each fixed lag. Pointwise separation at every fixed frequency is compatible
with Fourier averages tending to one, as the square-position source shows.
[Fixed-lag proof and control](../verification/ridout/README.md#repetitions-at-a-fixed-lag)

Run `python3 -m unittest discover -s tests -p test_lag_criterion.py`
for the exact enclosures, schedule checks, and rational controls.
