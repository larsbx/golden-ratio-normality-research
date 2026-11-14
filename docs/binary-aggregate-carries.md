# Aggregate signed carries and binary zero counts

Write $z_N=c_\alpha(1,0,N)$ for the original zero count on $[0,N)$,
$p_n=\max(T_n,0)$ and $P_N=\sum_{n<N}\min(1,p_n)$. The digits $d_n$
and coefficients $c_n$ are the actual complementary digits and their
convolution from [PR #8](https://github.com/larsbx/golden-ratio-normality-research/pull/8).
The proof uses those definitions at the accepted source revision
`d0b8b2df43572eac4cb2b0abb851bbe043c3b221`.

## Upper bound

Since $c_n,d_n\ge0$, the exact recurrence gives
$2p_n\le p_{n+1}+c_n$. For any half-open interval $[s,e)$ this gives

\[
\sum_{s\le n<e}p_n+p_s\le p_e+\sum_{s\le n<e}c_n.
\]

Every term in the origin convolution sum corresponds to one ordered pair
$(i,j)$ in the prefix with $i+j+1<N$. Its weight is $d_id_j\ge0$.
Summing over the entire square gives $z_N^2$. Thus

\[
P_N\le\sum_{n<N}p_n\le \sum_{n<N}c_n+p_N\le z_N^2+p_N.
\]

Here the lowercase $p_N$ is the positive part at the endpoint. The existing
pointwise bound gives $p_N\le z_N-1$ whenever $z_N>0$.

## Counting positive carries

Suppose $d_a=1$ and the following $L$ digits vanish. For $L\ge5$ set
$k=\lfloor(L-4)/2\rfloor$. The existing actual digit-window theorem gives
a complementary one at $j\in[k,2k+2)$. The pair $(a,j)$ forces a positive
coefficient at $a+j+1$. That index and the next two are inside the gap.
The three-zero trigger makes the carry there positive, and backward
propagation gives at least $k+1$ positive carries in the gap, including the
trigger position. Hence every
such gap costs at most twice its positive-carry count plus three.

Split the prefix into the initial zero segment, complementary ones, and
the zero gaps after them, including the terminal gap. The initial segment
has length at most one by the actual digit-window theorem at zero. Charging
each one and its following gap gives $N\le 2P_N+4z_N+1$. Since $z_N>0$
for $N\ge2$, the resulting finite theorem is

\[
\boxed{N\le 2z_N^2+6z_N-1\qquad(N\ge2)}
\]

In particular $z_N\ge(\sqrt{2N+11}-3)/2$. The new counting lemma is needed
to connect the aggregate estimate to prefix length, and it follows from the
existing source-specific recurrence and positivity theorems. The argument
is related to the positive-tail gap count in Bailey, Borwein, Crandall and
Pomerance, [Theorem 7.1](https://www.davidhbailey.com/dhbpapers/algebraic-bits.pdf).
The finite Lean theorem is the checked result. The real square-root formula
above is its algebraic consequence. All-block frequency convergence and
normality remain open.

## Half-prefix refinement

If both digit indices lie in $[\lfloor N/2\rfloor,N)$, their sum plus one
is at least $N$. This holds for both parities of $N$. The entire square of
that upper-half interval is therefore disjoint from the truncated convolution.
With $u_N=z_N-z_{\lfloor N/2\rfloor}$, Lean proves

\[
\sum_{n<N}c_n+u_N^2\le z_N^2,\qquad
N+2u_N^2\le 2z_N^2+6z_N-1\quad(N\ge2).
\]

Mixed pairs still contribute. At $N=5$, the two halves each contain one
complementary one, and the truncated convolution has mass three. This
attains equality in the pair bound and refutes retaining only the square
of the lower-half count. The correction is a finite two-scale constraint.
An improvement to the unconditional leading constant would require
further control on how zeros are distributed between the halves.

## Exact omitted pair count

Let $E_N$ count ordered pairs of original zero positions $i,j<N$ for which
$i+j+1\ge N$. The map $(n,i)\mapsto(i,n-1-i)$ has inverse
$(i,j)\mapsto(i+j+1,i)$ below the cutoff. Thus
$\sum_{n<N}c_n+E_N=z_N^2$ for every $N$, and the finite carry estimate gives

\[
N+2E_N\le 2z_N^2+6z_N-1\qquad(N\ge2).
\]

The upper-half square accounts for only one of the three omitted pairs at
$N=4$. Both mixed pairs lie on the cutoff, so the exact omitted count also
detects an off-by-one change to the cutoff. The formula does not provide an
unconditional asymptotic improvement without a further bound on $E_N$.

## Linear term at positive carries

Let $D_N$ count original zero positions $i<N$ with $T_i>0$. At such a
position, the signed recurrence charges three units of convolution mass.
Taking positive parts and telescoping retains this charge, giving
$\sum_{n<N}p_n+3D_N\le p_N+\sum_{n<N}c_n$. Combining this with the
gap count and exact omitted pair count gives

\[
N+2E_N+6D_N\le 2z_N^2+6z_N-1\qquad(N\ge2).
\]

The first nonzero correction occurs at $N=10$, from position nine.
This is a finite refinement, with the same unconditional square-root scale.

## Asymptotic consequence at arbitrarily late prefixes

The half-prefix bound at $N=2n$ can be written
$2n\le 4z_{2n}z_n-2z_n^2+6z_{2n}-1$. Suppose both counts satisfy
$z_m\le c\sqrt m$ at $m=n,2n$. On that rectangle the quadratic
$4xy-2y^2$, with $x=z_{2n}$ and $y=z_n$, is bounded above by its value
at $x=c\sqrt{2n}$ and $y=c\sqrt n$. First increase $x$, using $y\ge0$.
Then increase $y$, using $c\sqrt n\le c\sqrt{2n}$. It follows that

\[
2n\le 2(2\sqrt2-1)c^2n+6c\sqrt{2n}-1.
\]

Write $\delta=1-(2\sqrt2-1)c^2$. Whenever $n\ge1$ and
$\delta\sqrt n\ge3c\sqrt2$, the displayed inequality contradicts its
constant term $-1$. Hence for every such $n$, at least one of $n,2n$
exceeds the proposed envelope. In particular, when $c=73/100$ this
holds for every $n\ge16384$, using $\sqrt2\le1415/1000$ and
$\sqrt n\ge128$. It applies to each pair $(2^j,2^{j+1})$ with $j\ge14$.

For every nonnegative $c<1/\sqrt{2\sqrt2-1}$, the threshold is eventually
met, giving an unconditional lower bound of $1/\sqrt{2\sqrt2-1}$
on the limsup of $z_N/\sqrt N$. The per-prefix constant from the
earlier bound is $1/\sqrt2$ in the limit. The two-prefix guarantee does
not supply the larger constant at every sufficiently large prefix or
imply a digit frequency.

## Four checkpoints

At $N=4n$, in addition to the upper-half square, the omitted pairs
include the second quarter crossed with the fourth quarter, in both
orders. The three rectangles are disjoint. Thus

\[
E_{4n}\ge (z_{4n}-z_{2n})^2
       +2(z_{2n}-z_n)(z_{4n}-z_{3n}).
\]

At $N=8$, the two additional rectangles contribute one pair each.
The contribution survives at the exact cutoff convention used above.

Put $(a,b,d,x)=(z_n,z_{2n},z_{3n},z_{4n})$. The carry inequality now
gives $4n\le 4xa+4bd-2b^2-4ad+6x-1$. If all four checkpoints stay
under $0.76\sqrt N$, put $A=0.76\sqrt n$ and bound
$(a,b,d,x)$ by $(A,1.415A,1.733A,2A)$. The polynomial increases under
successively replacing $x,d,b,a$ by these bounds. The signs use
$a\ge0$, $b\ge a$, $1.733A\ge1.415A$, and $2A\ge1.733A$.
The resulting quadratic coefficient in $n$ is exactly $3.969457808$.
For $\sqrt n\ge512$, the gap to $4n$ dominates the linear term
$9.12\sqrt n$. Thus for every $n\ge262144$, at least one of
$n,2n,3n,4n$ exceeds $0.76\sqrt N$. In particular the limsup is at least
$0.76$. This establishes a bound at arbitrarily large prefixes.

## Equal-width partitions

For $N=kn$ and $f_i=z_{in}$, a row with index in block $i$ only
uses columns below $(k-i)n$. This gives

\[
\sum_{r<kn}c_r\le \sum_{i<k}(f_{i+1}-f_i)f_{k-i}.
\]

If $f_i\le g_i$ for all checkpoints, where $g$ is nondecreasing and
$g_0=0$, the right side is bounded by
$\sum_{i<k}(g_{i+1}-g_i)g_{k-i}$. First increase the weights using
$f_{i+1}-f_i\ge0$. Then use summation by parts with the decreasing
weights $g_{k-i}$ to increase the cumulative counts. The increments
themselves need not satisfy an entrywise upper bound.

For eight blocks, use the envelope $g_i=(31/40)\sqrt n\,s_i$ with
$s_i$ given by the numerators $(0,1000,1415,1733,2000,2237,2450,2646,2829)$
over 1000. These are checked rational upper bounds for $\sqrt i$.
The finite weighted sum for the $s_i$ is $6606938/10^6$. If every
checkpoint were below the $0.775\sqrt N$ envelope, the prefix bound
would give $8n\le 7.9365842725n+13.15485\sqrt n-1$, impossible
for $n\ge65536$. Hence at least one of the eight checkpoints exceeds
the envelope. The limsup is at least $0.775$.

## Integer square-root certificates

For scale $s>0$, set $u_0=0$ and
$u_i=1+\lfloor\sqrt{s^2i}\rfloor$ for $i>0$. The function $u_i$ is
nondecreasing and $u_i/s\ge\sqrt i$. For $b$ checkpoints the exact
integer budget is $Q=\sum_{i<b}(u_{i+1}-u_i)u_{b-i}$. If
$z_{in}\le c\sqrt{in}$ at all checkpoints, the partition bound gives

\[
bn\le(2c^2Q/s^2)n+6c(u_b/s)\sqrt n-1.
\]

For $s=10000$ and $b=64$, the exact values are $Q=5063329433$
and $u_b=80001$. With $c=397/500$, the quadratic margin
$64-2c^2Q/s^2$ is positive, and at $\sqrt n\ge256$ it absorbs the
linear term. Therefore for each $n\ge65536$ at least one of the 64
checkpoints satisfies $z_{in}>0.794\sqrt{in}$. In particular the limsup
is at least $0.794$. The conclusion concerns zero counts on the
square-root scale.

## The limiting checkpoint constant

For $K$ blocks, the exact square-root envelope uses the weighted sum
$S_K=\sum_{i<K}(\sqrt{i+1}-\sqrt i)\sqrt{K-i}$. On
$[\sqrt i,\sqrt{i+1}]$, one has
$\sqrt{K-i}\le\sqrt{K-x^2}+1$ because $x^2\le i+1$.
Integrating on each interval and summing gives
$S_K\le K\pi/4+\sqrt K$. The integral of the quarter circle is obtained
from the pinned mathlib semicircle integral by reflection and scaling.

If every checkpoint of width $n$ satisfies $z_{in}\le c\sqrt{in}$,
the resulting carry budget is
$Kn\le2c^2n(K\pi/4+\sqrt K)+6c\sqrt{Kn}-1$.
For $\pi c^2<2$, take $K$ to be a square with sufficiently large root
and $n\ge2$. The positive margin
$1-\pi c^2/2$ contradicts the budget once
$\sqrt K>(2c^2+6c)/(1-\pi c^2/2)$. Taking $n$ beyond any requested
threshold gives a prefix above $c\sqrt N$. Thus the limsup lower bound
is $\sqrt{2/\pi}\approx0.79788456$. The argument establishes an
arbitrarily-late exceedance on the square-root scale.

The partition-to-integral strategy has a precedent for the ones of
$\sqrt2$ in Remark 1 of [On the binary digits of $\sqrt2$](https://math.colgate.edu/~integers/s30/s30.pdf).
Here the input is the original zero count and the lower carry budget
comes from the signed quadratic, yielding a different constant.

## A constant error and a finite checkpoint window

The rectangle over $[\sqrt i,\sqrt{i+1}]$ already lies under
$\sqrt{K+1-x^2}$. Indeed $x^2\le i+1$ implies $K-i\le K+1-x^2$.
The integrand is nonnegative on the remaining interval from $\sqrt K$
to $\sqrt{K+1}$. The scaled quarter-circle integral therefore gives
the stronger bound $S_K\le (K+1)\pi/4$. Its additive error relative to
$K\pi/4$ is at most $\pi/4$ for every $K$.

Take $K=16384$ and $c=3989/5000$. Since $\pi<3.1416$,
$K-c^2(K+1)\pi/2>2.4345$. For $\sqrt n\ge256$ this margin absorbs
$6c\sqrt K=612.7104$. Hence for every $n\ge65536$, some checkpoint
$i n$ with $1\le i\le16384$ satisfies $z_{in}>0.7978\sqrt{in}$.
This gives a finite window for a constant near the previously proved
limsup bound.

## Limit of the checkpoint sum

On the same interval $[\sqrt i,\sqrt{i+1}]$, the integrand of
the quarter circle of squared radius $K$ is bounded above by
$\sqrt{K-i}$. The checkpoint rectangle therefore covers that part
of the quarter circle. Together with the larger circle comparison,
this gives the two-sided estimate

\[
\frac{K\pi}{4}\le S_K\le\frac{(K+1)\pi}{4}.
\]

For $K>0$, the normalized sum differs from $\pi/4$ by between zero
and $\pi/(4K)$. Lean checks convergence of $S_K/K$ to $\pi/4$.
This identifies the leading coefficient of the specific square-root
envelope calculation. Refining this partition estimate alone cannot
lower that coefficient below $\pi/4$. A larger limsup bound from
the carry approach would need more information, such as a stronger
lower carry budget or additional constraints on the actual zero positions.

## Replay and adversarial controls

Run `python3 -m unittest discover -s tests -p test_aggregate_carries.py -v`
for exact integer controls, and `python3 tools/verify.py --output
build/replay-aggregate-carries` for the pinned project gate. The oracle
reconstructs floors from integer square roots and carries from their
defining floor products. Actual positions 5 and 13 witness, respectively,
failure of the two-zero trigger and failure of the shifted estimate with
the right boundary deleted. Only two of the first eight carries are positive,
so an unconditional half-prefix count would also be false.
