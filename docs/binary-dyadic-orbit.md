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
