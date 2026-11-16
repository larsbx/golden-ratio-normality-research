# Scheduled binary frequency 3

Research review against PR #41 head `2649ad79984d9b3d8abcbc3efdb8723a80223a8a`. Its tree agrees with the merge commit `19cbf785790d8567749005402a0e1c55a8f2cd86`. The modified proofs and replay in this review are separate from the successful [Foundation acceptance](https://github.com/larsbx/golden-ratio-normality-research/actions/runs/43883297643) and [Ridout proof replay](https://github.com/larsbx/golden-ratio-normality-research/actions/runs/43883297557) on the base revision.

Let `e(t) = exp(2πit)`, `α = (√5−1)/2`, `B_n = 2^n`, `a_n = floor(B_n α)`, and `p_N = a_N/B_N`. The repository's exact modular mean is
`A_h(N) = (1/N) Σ_{0≤n<N} e(h B_n p_N)`.
The selected scheduled frequency is `h(2^(2^|h| d)−1) = 3` with `h=d=1`. Use `N>0` throughout.

## Exact correlation target

Set `z_n = e(B_n p_N)` for the entire orbit of this single rational seed, including indices `N` and `N+1`. Then

```text
z_(n+2) conj(z_n) = e(3 B_n p_N)

Re A_3(N) = 1 − (1/(2N)) Σ_{0≤n<N} |z_(n+2) − z_n|².
```

This uses all `N` differences. Trimming the sum to pairs with both indices below `N` changes the total energy by at most 8. The formal conditional lemma makes `Re A_3(N) ≤ ε` equivalent to the total energy being at least `2N(1−ε)`. The scheduled eventual upper bound is equivalent to the energy per start having liminf at least 2. Replacing `p_N` by `α` changes `A_3(N)` by at most `6π/N` by the existing dyadic prefix estimate.

A separate exact relation records how adjacent real parts contribute. Put `u_n = Re z_n`, `μ = (1/N) Σ u_n`, `ν = (1/N) Σ u_(n+1)`, and use the paired indices `0≤n<N` for covariance. The product-to-sum identity gives

```text
Re A_3(N) = 2 Cov_N(u_n,u_(n+1)) + (2ν−1) μ,
ν−μ = (u_N−u_0)/N.
```

So even a proof of first-mode cancellation would leave a required upper bound on the adjacent cosine covariance. The finite data below include both signs of that covariance for the actual source. The cosine product identity and the lag-two complex difference identity use different observables of the same orbit.

## Source-specific integer transfer

Let `b=1−α`, `q_n=floor(B_n b)`, `t_n=B_n b−q_n`, `D_n=3B_n−2q_n`. Use the repository's signed carry `T_n` and uncarried suffix `U_n` for `b`. Its signed quadratic residual satisfies

```text
P_n = q_n² − 3B_n q_n + B_n² = U_n − B_n T_n = t_n(D_n−t_n).
```

The number `β = 3b−1 = 2−3α = α⁴` obeys `β²−7β+1=0` and lies in `(0,1)`. Thus `e(3B_n α)=conj(e(B_n β))`. Write `r_n=floor(B_n β)`. The exact transfer is

```text
j_n = floor(3 t_n) ∈ {0,1,2}
j ≤ j_n  iff  3D_n j − j² ≤ 9 P_n     (j ≤ 2)
r_n = 3q_n − B_n + j_n
R_n = r_n² − 7B_n r_n + B_n²
    = 9(U_n − B_n T_n) − 3D_n j_n + j_n².
```

At `n=0,j=10` the residual comparison holds and the branch inequality fails, showing why the upper restriction is needed. The branch test factors the difference as `(3t_n−j)(3D_n−3t_n−j)`. The second factor is positive since `b<1/2`, `D_n≥2B_n≥2`, and `t_n<1`. The residual identity follows by substitution. For an independent integer recurrence, let `d_n=r_(n+1)−2r_n` and `G_n=7B_n−2r_n`. Then

```text
d_n = 1_[4 R_n ≥ 2 G_n − 1]
R_(n+1) = 4 R_n − d_n (2 G_n − 1).
```

In fact `f_B(y)=y²−7By+B²` decreases strictly on `[0,B]`, has its irrational small root at `Bβ`, and `f_(2B)(2r_n+1)=4R_n−2G_n+1`. The sign comparison therefore selects the actual next digit. These identities map the carries to the actual phase energy through `4 sin²(π(B_n β−r_n))`. They preserve the joint order of the phase terms. They supply exact digits and phase correlations at finite widths, with no estimate on the distribution of the residuals as the width grows.

## Unconditional paired deficit

Let `M_N` count adjacent changes among the first `N` digits of `β` and `c_N=3−j_N∈{1,2,3}`. The floor identity gives `2B_N−3a_N = r_N+c_N`. The frequency-three modular phases are therefore the conjugates of the frequency-one phases of `(r_N+c_N)/B_N`. Replacing that rational seed by `r_N/B_N` costs at most `δ_N=2π c_N(1−2^(−N))` in the unnormalized sum, by the geometric sum and the phase Lipschitz estimate.

For the latter rational seed, a digit change puts its phase in the closed left half-circle. The existing frequency-one paired argument applies to this seed. With phase `v_n`, `v_(n+1)=v_n²`, so each counted pair has `|v_n+v_(n+1)|≤√2`. Counting the two endpoints once gives the second inequality. Taking real parts term by term gives the first.

```text
Re (N A_3(N)) ≤ N − M_N + δ_N
    |N A_3(N)| ≤ N − (1−1/√2) M_N + δ_N.
```

There is also a reverse real-deficit bound. If `r≥1` equal bits remain in a run of the finite `β` prefix, the corresponding tail of `r_N/B_N` has distance at most `2^(−r)` from an integer. Its real deficit is at most `1−cos(2π 2^(−r))`. Summing each run gives the bound with the finite constant

```text
K = Σ_{r≥1} [1−cos(2π 2^(−r))] ≤ 3 + π²/24,
N − Re(N A_3(N)) ≤ K(M_N+1) + δ_N.
```

The constant bound keeps the first two terms exactly and bounds the rest by `2π² 4^(−r)`. In particular, `A_3(N)→1` is equivalent to `M_N/N→0`. The reverse complex implication follows from the real deficit via `|1−A|²≤2(1−Re A)` for `|A|≤1`.

An elementary explicit bound follows directly from the quadratic norm. For `y=B_n β−r_n`, the positive integers `f_B(r_n)` and `−f_B(r_n+1)` factor as `y(G_n−y)` and `(1−y)(G_n−1−y)`. Both co-factors are positive and less than `7B_n`, so `min(y,1−y)>1/(7B_n)`. A constant run starting at `n` has length at most `n+2`. Windows from `s_i=2^(i+1)−2` through `s_(i+1)` each force one change; they share an endpoint and have disjoint adjacent pairs. Thus `M_N≥k` for `N≥2^(k+1)−1`. This yields an explicit logarithmic unnormalized deficit up to the bounded displacement. As an application of published work, Bugeaud and Evertse, Theorem 3.1, yields `M_N ≫ (log N)^(3/2)/sqrt(log log N)` eventually for this degree-two algebraic irrational. Both lower bounds are on the unnormalized deficit. The corresponding normalized lower bounds can tend to zero. [On two notions of complexity of algebraic numbers](https://www.impan.pl/shop/en/publication/transaction/download/product/83574)

The modulus bounds can also be made exact at each fixed modular numerator without a displacement term. Count changes in the `N`-bit representation of `3a_N mod B_N`, using leading zeros. The same ordered-pair proof bounds the complex sum in modulus by `N−(1−1/√2)·count` and its real part by `N−count`. The integer replay checks both inequalities at the reported widths.

## Controls

**Square-position source.** For `ξ=Σ 2^(−j²)`, the same fixed-multiplier separation holds and every fixed Fourier mean tends to 1, as proved in [the Ridout review](https://github.com/larsbx/golden-ratio-normality-research/blob/2649ad79984d9b3d8abcbc3efdb8723a80223a8a/verification/ridout/README.md#repetitions-at-a-fixed-lag). Its lag-two energy tends to zero. Any lower bound near `2N` based on pointwise separation alone would fail here.

**Fixed irrational with first-mode cancellation.** Make a binary expansion by concatenating the stages `0^j 1^j (01)^(2j)` for `j=1,2,…`. It is irrational because it has both unbounded runs and infinitely many changes. Its digit balance tends to one half and its change density to two thirds. The first two runs of each stage occupy one third of the starts and shadow the zero point of the doubling map (the all-one tail has phase one as well). The alternating run occupies two thirds and shadows the orbit `{1/3,2/3}`. If `r` bits of a run remain, the orbit and its shadow differ by at most `2^(−r)` in circle distance, so replacing them changes each fixed-frequency partial sum by `O_h(1)` per run. Complete alternating runs have even length. The incomplete last stage costs `O_h(√N)`, as do the total run errors. The first average tends to `1/3+(2/3)(−1/2)=0` and the third tends to 1. The same limits hold for the exact modular truncations by the geometric perturbation bound.

For separation, take `n` in stage `j` and let `m≥n` be the start of stage `j+1`. Then `m−n≤6j` and `n≥3(j−1)j`. The tail at `m` starts with `j+1` zeros followed by a one. For each fixed nonzero integer `h`, eventually the nearest-integer distance of `h2^m ξ` is `|h|{2^m ξ}≥2^(−j−2)`. Since `||2^k y||≤2^k ||y||` for distance to the nearest integer, `||h2^n ξ||≥2^(−7j−2)`. For every fixed positive `B` this implies `2^n ||h2^n ξ||^B≥1` eventually. The example satisfies the general ordered first-mode estimate, has positive limiting transition density and satisfies the all-fixed-multiplier separation simultaneously. It rejects an implication from those properties and first-mode cancellation to the scheduled upper bound at frequency 3. It also gives limiting cosine covariance `1/2`.

**Complete-frequency invariance.** For odd numerator `p`, multiplication by `p` permutes the full frequency labels modulo `2^N`. Even the complete distribution of phase sums is shared with the numerator-one family. With the seed `1/2^N`, its third average tends to 1 by the geometric tail estimate and its lag-two energy tends to zero. The permutation modulo `2^N` is checked at small widths independently of the exact golden source.

**Actual short-prefix square-root cap.** At `N=4` the actual numerator is 9. Outward-rounded integer arithmetic gives `−2.08979022 < Re(4 A_3(4)) < −2.08979021`, hence `|4 A_3(4)|>√4`. This rejects an all-width unit-constant square-root bound, without deciding any asymptotic square-root estimate.

## Replay and remaining obligation

```sh
python3 tools/replay_third_frequency.py
lake build GoldenNormality.BinaryThirdFrequency
lake env lean tools/ThirdFrequencyAudit.lean
```

Use the pinned root Lean and Mathlib revisions. The Python replay cross-checks both floor computations through width 2,048 and signed carry suffixes through width 128. It computes the finite modular correlations using the existing integer half-angle enclosure and checks their exact real and norm deficit inequalities. At `N=32768` it certifies `Re A_3∈[−0.00669712,−0.00669711]` and mean lag-two energy in `[2.01339422,2.01339423]`. At widths `M` within 200 of 32,768 the modular real third mode is strictly negative. Indeed, compare the two rational dyadic prefixes at the shorter width. Their difference is smaller than one unit at that width, so the common phase sum differs by at most `6π`, with at most `|M−32768|` additional terms. This also gives negativity for the actual sums on that same interval. The covariance is positive at widths 128 and 512 and negative at 32, 2,048, 8,192, 16,384, and 32,768. These samples delimit finite values of the exact modular means.

The Lean change covers the source transfer, the branch/residual algebra, the modular lag-two equality and the finite energy threshold. The paired beta bounds, run argument and irrational control above are written deductions. The remaining proof obligation at mode 3 is a lower bound `2−o(1)` on the mean lag-two energy along the actual signed quadratic recurrence, or an equivalent one-sided covariance estimate with the displayed mean correction. Establishing it for mode 3 would discharge one scheduled lag. The other scheduled modes retain their own eventual hypotheses.

The [signed tail count follow-up](binary-scheduled-third-tail-counts.md) gives exact rational cutoff decisions, a finite count criterion for this obligation, and a fixed-depth counterexample.
