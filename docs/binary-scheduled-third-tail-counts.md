# Signed tail counts for scheduled frequency three

This is a follow-up to the [frequency-three review](binary-scheduled-third-frequency.md) on base revision `2649ad79984d9b3d8abcbc3efdb8723a80223a8a`. It gives an integer criterion for the first scheduled real upper bound and an obstruction to replacing that criterion by agreement at a fixed block depth.

## Exact rational comparisons from the quadratic

Use `β=2−3α`, where `α=(√5−1)/2`. For `B_n=2^n`, set

```text
r_n = ⌊B_n β⌋          y_n = B_n β − r_n
G_n = 7 B_n − 2 r_n    R_n = r_n² − 7 B_n r_n + B_n²
```

The polynomial `β²−7β+1=0` gives `R_n=y_n(G_n−y_n)`. Here `0<y_n<1` and `G_n≥5B_n`. For any integers `a≤m` and `m>0`, the exact test is

```text
a/m ≤ y_n  iff  a m G_n − a² ≤ m² R_n.
```

Indeed the difference on the right factors as `(m y_n−a)(m G_n−m y_n−a)`, with positive second factor. The test also works at rational endpoints 0 and 1. Cutoffs outside the upper hypothesis require a different argument. For example, at `n=0,m=1,a=8` the right side is true and the left side is false. The residual can be taken directly from the earlier signed-carry transfer. It can also be advanced by the separate exact recurrence for `R_n`.

For a dyadic grid of denominator `H=2^k`, let `v_n=⌊H y_(n+1)⌋`. The cutoff rule determines `v_n` by integer comparisons. A second exact evaluation uses `v_n=r_(n+k+1)−H r_(n+1)`. The replay uses the independent square-root floor formula for both the small scaled-floor comparison check and bulk prefix counting.

## The signed count criterion

Let `d_n=r_(n+1)−2 r_n`, so `y_n=(d_n+y_(n+1))/2`. Define `s_n=+1` when `d_n=d_(n+1)` and `s_n=−1` otherwise. Folding the next tail toward the nearest integer gives

```text
u_n = min(y_(n+1), 1−y_(n+1))
cos(2π y_n) = s_n cos(π u_n).
```

The two neighboring digits determine the sign, and the folded next tail determines its weight. For `H=2^k` and `0≤j<H/2`, count `P_j` positive signs and `M_j` negative signs with `min(v_n,H−1−v_n)=j` among `0≤n<N`. This bin implies `j/H≤u_n≤(j+1)/H`. Write `c_j=cos(πj/H)`, and define

```text
L_(k,N) = (1/N) Σ [P_j c_(j+1) − M_j c_j]
U_(k,N) = (1/N) Σ [P_j c_j − M_j c_(j+1)].
```

The actual mean `V_N=(1/N) Σ cos(2π 3·2^n α)` lies in this interval because `cos(2π 3·2^n α)=cos(2π y_n)` and the cosine decreases on this half interval. Every term has width at most `π/H` by the derivative bound, so the full interval also has that width. With exact coefficients, dyadic refinement increases the lower bound and decreases the upper bound. The modular `Re A_3(N)` lies between `L_(k,N)−6π/N` and `U_(k,N)+6π/N` by the prior prefix estimate. The finite replay uses outward integer enclosures for `c_j` and `6π<132/7`. Its printed intervals account for these roundings.

In particular, the original eventual upper bound is equivalent to

```text
inf_(k≥1) limsup_(N→∞) U_(k,N) ≤ 0.
```

The proof takes the width error `π/2^k` after the limsup in `N`. With `C_j=Σ_(i≤j)(P_i−M_i)`, the main term in the upper bound is

```text
(1/N) Σ (P_j−M_j)c_j = (1/N) Σ C_j(c_j−c_(j+1)).
```

The weights are nonnegative and sum to 1. The remaining upper correction is `(1/N) Σ M_j(c_j−c_(j+1))≤π/H`. Thus a sufficiently fine grid and upper bounds on the weighted cumulative imbalance suffice. Requiring every cumulative count to be nonpositive can discard valid certificates. The actual source has positive cumulative imbalance at some bins even when the upper Fourier bound is certified negative. An asymptotic example on the transformed-source side comes from stages `0^j 1^j (01)^(3j)`. They spend one quarter of the starts near the fixed orbit and three quarters near the alternating orbit. The real average approaches `1/4−3/8=−1/8`, while the cumulative imbalance at cutoff `1/8` tends to `1/4`. These limits follow by bounding the total phase approximation error by a constant per run and the number of starts near a cutoff boundary by a constant per run.

## An obstruction at every fixed block depth

For each finite depth `K`, there is a fixed irrational `x∈(0,1)` with all of the following properties.

- Both `x` and `y={−3x}` have uniform limiting frequencies for every binary block of length at most `K`.
- Every Fourier average of `x` at an integer frequency indivisible by 3 tends to zero.
- The real third Fourier average of `x` tends to a strictly positive constant.
- For every nonzero integer `h` and positive integer `B`, the inequality `||h 2^n x||≥2^(−n/B)` holds eventually, where the norm is distance to the nearest integer.

Choose an even block length `L≥max(4,K+1)`. Form the binary expansion of `y` by independently sampling uniform length-`L` words of parity sign `σ=(−1)^(L/2+1)`. Each proper subset of coordinates within a word is independent and fair, since specifying those coordinates leaves at least one bit to absorb the parity constraint. A window of length at most `K` therefore has the fair distribution at every alignment, including windows crossing a block boundary.

At each `n` write `y_n={2^n y}`. Choose a fiber state `k_0` uniformly from `{1,2,3}` independently of the future blocks, and set `x=(k_0−y)/3`. If `b_n` is the leading bit of `y_n`, the lifted states satisfy `k_(n+1)≡2k_n−b_n mod 3` and `{2^n x}=(k_n−y_n)/3`. At block boundaries this is a random walk on residues modulo 3 with step equal to the negative integer value of the fresh word, since `2^L≡1 mod 3`. Either parity admits at least two distinct residues. For odd parity use values 1 and 2, and for even parity use 0 and 5. The two nontrivial Fourier eigenvalues of this three-state walk are convex combinations of at least two distinct cube roots of unity, so their absolute values are bounded by some `ρ<1`. The distribution of the boundary state after `v` blocks differs from uniform by `O(ρ^v)`, uniformly in its starting state.

Here is a direct justification of the required orbit averages. For a bounded observable of the boundary state and a fixed finite forward window of blocks, two observations whose windows are separated by `v` blocks have covariance `O(ρ^v)`. Condition on the blocks and state of the earlier window, then apply the mixing bound across the gap before sampling the later window. Overlapping windows contribute only a bounded number of covariance terms per start. The variance of the sum of `N` observations is therefore `O(N)`. Chebyshev's inequality at `N=j^2` and Borel–Cantelli yield convergence to the expectation along squares. Boundedness and the gap `2j+1=o(j^2)` extend it to all `N`. Apply this at each alignment and to finite tails of increasing length. Uniform approximation of the phase functions gives the Fourier limits on a common probability-one set. Finite binary block indicators use only the current state and a finite window of bits as below.

For each alignment the fiber state is uniform, independently of its current tail. Taking the average over three fibers gives a zero phase sum whenever the frequency is indivisible by 3. Binary cylinders for `x` are fair at depth `j≤K` as well. For each depth-`j` cell of `y_n`, the membership of each of its three lifted points in the depth-`j` cells of `x` is constant away from endpoints. Across uniform cells and fibers, each depth-`j` cell of `x` has exactly three contributions, counting multiplicities. This follows because the image of that cell under the degree-three circle map consists of three cells of length `2^(−j)`, counting multiplicities. Endpoints have probability zero from the cylinder bound below.

It remains to evaluate the real phase at frequency one of `y`. At any nonzero offset inside a block, the first digit of the remaining proper suffix is fair independently of all following digits, so the phase expectation is zero. At offset zero, write `y=(W+Y)/2^L`, with word value `W` and independent tail `Y`. With `e(t)=exp(2πit)`, the word factor is

```text
E e(W/2^L) = σ 2^(−L) Π_(j=1)^L (1−e(2^(−j))).
```

The unrestricted uniform term vanishes at this frequency. Since `L` is even, complementing each block preserves the law, so `Y` is symmetric about `1/2` and `E e(Y/2^L)=e(2^(−L−1)) C`, where `C=E cos(2π (Y−1/2)/2^L)≥cos(π/2^L)>1/2`. Factoring each factor in the product shows that the combined phase has sign `σ(−1)^(L/2+1)=+1`. Since `e(3x)=conj(e(y))` and block boundaries have density `1/L`, the real third mean of `x` is

```text
(C/L) Π_(j=1)^L sin(π 2^(−j)) ≥ 2^(−L(L−1)/2)/(2L) > 0.
```

The inequality uses the chord bound for sine on `[0,π/2]`. In particular its modular third average has the same positive limit by the same dyadic truncation argument as for the actual source.

For separation, any specified binary tail window of length `p` pins at least `max(0,⌊p/L⌋−1)` complete independent blocks. Its probability is at most `2^(-(L−1)max(0,⌊p/L⌋−1))`, uniformly in the start. The event `||h 2^n y||<2^(−n/B)` is covered by a bounded number of binary cylinders of depth `⌊n/B⌋`, where the bound can depend on `h`. Its probabilities are summable over `n`. Borel–Cantelli and a countable intersection give separation for all fixed `h,B` on the same set of full probability. Since `||h 2^n y||≤3||h 2^n x||`, the result for `y` with `B+1` gives the claimed result for `x` with `B`. In particular the chosen (x) is irrational, since a rational would have zero distance for a multiplier equal to its denominator. Choose one realization satisfying all these properties. The constructed source depends on the chosen depth. This rejects inferring the exact limiting sign from a fixed depth, even with separation and cancellation at every frequency indivisible by 3. The weighted count criterion retains the limit over growing depth.

## Reproduction and proof status

```sh
python3 tools/replay_third_tail_counts.py
lake build GoldenNormality.BinaryThirdFrequency
lake env lean tools/ThirdFrequencyAudit.lean
```

The integer replay checks 10,240 rational cutoffs against separate scaled floors and verifies the finite parity and fiber laws for several block lengths. It compares smaller certificates with the prior modular replay. At 524,288 starts the certified modular mean lies in `[−0.00089622, −0.00033574]`. At 1,048,576 starts it lies in `[0.00028535, 0.00044336]`. A separate count of dyadic phase cells of the original numerator `3⌊2^N α⌋ mod 2^N` also certifies the positive sign there, using its own cosine enclosure. For two widths `M,N`, their unnormalized modular sums differ in real part by at most `|M−N|+6π`. This follows by comparing the two rational seeds over the shorter prefix and bounding the extra terms by one each. The replay uses that bound to certify a positive modular real mean at every width from 1,048,320 through 1,048,832. The written proof handles arbitrary block length and almost-sure convergence. The finite enumerations check its local combinatorics. See the review receipt for the exact Lean status.

The same written reduction applies to a fixed positive scheduled multiplier `h`. With `m=⌈hα⌉`, replace `β` by `m−hα`. Its polynomial is `X²−(2m+h)X+(m²+hm−h²)`, and the derivative parameter becomes `(2m+h)B_n−2r_n≥2`. Substituting that new residual in the factorization gives the same integer cutoff and signed-count bounds. The modular displacement is at most `2πh/N` for this fixed mode. The recorded Lean specialization and finite certificates in this review use `h=3`.

The next proof obligation is a source-specific eventual bound on the weighted cumulative imbalance at arbitrarily fine resolution. It must use the joint distribution of `(d_n,d_(n+1),R_(n+1),G_(n+1))` along the actual quadratic orbit. This formulation specifies which arithmetic events to bound, and the fixed-depth controls distinguish it from an inference based on one depth or on pointwise separation.
