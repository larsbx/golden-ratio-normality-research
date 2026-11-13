# Actual binary complements and finite signed carries

This increment connects the original zero-count problem to the actual binary
expansion of the complementary quadratic irrational, and develops finite carry
identities with all coefficient signs retained. It proves exact transformations,
pointwise carry bounds, and conditional positivity results. The aggregate
estimate needed for a square-root zero-count bound remains a separate obligation.

Write

\[
\alpha=\varphi-1=\frac{\sqrt5-1}{2},\qquad
\beta=1-\alpha=\frac{3-\sqrt5}{2}.
\]

Both numbers lie strictly between zero and one, and

\[
\alpha^2+\alpha=1,\qquad \beta^2-3\beta+1=0.
\]

The negative coefficient in the second polynomial is essential. The existing
positive-polynomial sparsity proof for the original one count cannot simply
be applied with `alpha` replaced by `beta`.

## Exact source and width conventions

Let `q_alpha(n) = floor(2^n*alpha)` and `q_beta(n) = floor(2^n*beta)`.
The original prefix certificate and integer polynomial obstruction prove
strict dyadic nonintegrality. Consequently, at every natural `n`, including zero,

\[
\boxed{q_\beta(n)=2^n-1-q_\alpha(n).}
\]

The `-1` is necessary: omitting it already fails at `n=0`. The proof concerns
the real floor functions; a convention about flipping a supplied finite word
does not establish this identity.

Digits are zero-indexed after the radix point:

\[
d_n^\beta=q_\beta(n+1)-2q_\beta(n)=1-d_n^\alpha.
\]

For a block beginning at `start` with width `length`,

\[
B^\beta_{start,length}=q_\beta(start+length)-2^{length}q_\beta(start)
 =2^{length}-1-B^\alpha_{start,length}.
\]

The module also proves nonnegativity and the strict binary range of these
digits and blocks. A finite original prefix certificate transfers to an actual
complementary floor only when the exact equation `q+r+1=2^n` is supplied.

`BinaryComplement.actualDigits` is defined directly from the complementary
real-number digit function. Its equality to the pointwise complement of the
original actual word is then proved. `BinaryComplement.powerDigits` maps
`d` to `1-d` on the proved original power evaluator; its source identity,
length, and positional value are likewise proved. Leading zeros are retained.
For example, the complementary first two digits are `[0,1]`, of width two and
value one. Erasing that width changes the block being discussed.

## Counts and the normality target

Define `flipValue k j = 2^k-1-j`. On the explicit range `j<2^k`, this map stays
in range and is an involution. The range hypothesis matters because natural
subtraction truncates for invalid inputs.

Let `c_beta(k,j,N)` count the actual complementary width-`k` block with value
`j` at every starting position `0,...,N-1`, with overlaps retained. Then

\[
\boxed{c_\beta(k,j,N)=c_\alpha(k,2^k-1-j,N)}\qquad(j<2^k).
\]

The same `k` and `N` occur on both sides. For positive width and positive `N`,
the observation uses the complete prefix of `N+k-1` digits. In particular,

\[
c_\beta(1,1,N)=c_\alpha(1,0,N),\qquad
c_\beta(1,0,N)=c_\alpha(1,1,N).
\]

The finite digit sum is also identified with these actual counts:

\[
\sum_{i<N}d_i^\beta=c_\beta(1,1,N)=c_\alpha(1,0,N).
\]

Finally, the exact complementary binary normality proposition is equivalent
to `GoldenNormality.NormalInBase 2`. It retains every positive width, valid
block value, positive tolerance denominator, positive eventual threshold, and
all later `N`. This is an equivalence between two open propositions; neither
side is proved by the transformation.

## A finite signed carry model

For the remainder of this document, `d_i` and `q_N` refer to the actual
complementary number. Put `B_N=2^N` and

\[
P(B,q)=q^2-3Bq+B^2,\qquad P_N=P(B_N,q_N).
\]

Signed integer arithmetic is used throughout. The exact update is

\[
P(2B,2q+d)=4P(B,q)+2d(2q-3B)+d^2.
\]

For the actual complementary floors, the transferred original certificates
give the uniform residual bounds

\[
\boxed{0<P_N<3B_N.}
\]

The finite quadratic coefficient indexed by `N` belongs to the fractional
binary place **`N+1`**:

\[
c_N=\sum_{i<N}d_i d_{N-1-i},\qquad a_N=c_N-3d_N.
\]

Thus `c_0=0`, and `c_1=d_0^2`. The digit index and the coefficient's binary
place must not be confused. Define the high and remaining finite convolutions

\[
C_N=\sum_{i<N}d_i q_{N-1-i},
\]

\[
U_N=\sum_{i<N}d_i\,2^{N-1-i}
      B^\beta_{N-1-i,i+1}.
\]

All three of `c_N`, `C_N`, and `U_N` are nonnegative. Weighted reconstruction
of `q_N` from its digits and the exact block identity prove

\[
q_N^2=B_N C_N+U_N,\qquad C_{N+1}=2C_N+c_N.
\]

Here **`U_N` is an uncarried convolution suffix**. It may exceed `B_N`.
At the actual prefix `N=4`, one has `q_4=6`, `C_4=1`, and `U_4=20>16`.
Replacing it by the Euclidean remainder of `q_N^2` modulo `B_N` is false.

Define the signed carry

\[
T_N=3q_N-B_N-C_N.
\]

The formal development proves all of the following finite identities:

\[
\boxed{T_0=-1,\qquad 2T_N=T_{N+1}+a_N,\qquad
B_NT_N=U_N-P_N.}
\]

It also proves the explicit polynomial truncation formula

\[
T_N=-2^N-\sum_{i<N}a_i2^{N-1-i}.
\]

Every object is built from actual source floors or digits. No infinite series,
convergence assumption, or freely chosen recurrence solution is substituted
for these finite definitions.

## Bounds and positivity

The residual bounds and `U_N>=0` imply `T_N>-3`. Since `T_N` is an integer,
this gives `T_N>=-2`. Bounding each suffix block by its binary scale gives

\[
U_N\le B_N\sum_{i<N}d_i.
\]

Using `P_N>0` in the exact carry identity then yields the pointwise bound

\[
\boxed{-2\le T_N<\sum_{i<N}d_i=c_\alpha(1,0,N).}
\]

The lower bound is sharp at `N=1`, where `T_1=-2`. This is a pointwise bound;
summing it naively does not supply the desired quadratic aggregate estimate.

If `d_N=0`, then `a_N=c_N>=0`, and the recurrence proves

\[
T_{N+1}>0\quad\Longrightarrow\quad T_N>0.
\]

Induction propagates this positivity backward over any supplied interval of
actual zero digits. The interval has the precise hypothesis
`start <= i < start+length`, with positivity supplied at `start+length`.

A further local trigger supplies positivity without assuming a positive carry:

\[
\boxed{c_N>0,\quad d_N=d_{N+1}=d_{N+2}=0
       \quad\Longrightarrow\quad T_N>0.}
\]

Otherwise the recurrence would force `T_(N+1)<=-1`, then `T_(N+2)<=-2`,
then `T_(N+3)<=-4`, contradicting the universal lower bound. The actual
instance `N=3` satisfies this trigger. Dropping the third zero fails at `N=5`:
`c_5=1`, `d_5=d_6=0`, but `T_5=0`.

## Controls and acceptance

The positive controls prove their finite source bindings from exact original
prefix certificates. Among the retained counterexamples are:

| Actual case | Invalid variation it detects |
| --- | --- |
| Complementary floor at scale zero is zero. | Dropping the floor identity's `-1`. |
| Complementary prefix `[0,1]` and shifted segment `[1,1]`. | Erasing width or resetting a shifted source to zero. |
| Original first three digits `[1,0,0]`, complement `[0,1,1]`. | Failing to swap zero and one counts. |
| `T_1=-2`. | Assuming carries are nonnegative or strengthening the lower bound to `-1`. |
| `T_2=-1` and `T_3=1`. | Backward positivity without its zero-digit hypothesis. |
| `T_4=1`, `T_5=0`, and `d_4=0`. | Forward positivity through a zero digit. |
| `U_4=20>16`. | Treating the finite suffix as a bounded Euclidean remainder. |
| `c_5=1`, `d_5=d_6=0`, and `T_5=0`. | Removing the third zero from the positivity trigger. |

Explicit public theorem-type wrappers retain the source, signs, indices, and
quantifier order. Isolated negative controls must each fail for their intended
logical reason. The full gate fresh-compiles the project, inspects every
compiled declaration's transitive assumptions, and reruns the inherited native
conformance, finite receipt, and receipt-type checks.

Replay with the pinned tools described in the root README:

```sh
python3 tools/verify.py --output build/replay-binary-complement
```

Acceptance requires a clean committed checkout and a new output directory.
The report identifies the exact source revision and hashes. The proof increment
adds no native producer, execution bound, dependency pin, or universal native
implementation-refinement claim.

## Literature and remaining obligation

Bailey, Borwein, Crandall, and Pomerance,
[*On the binary expansions of algebraic numbers*](https://www.davidhbailey.com/dhbpapers/algebraic-bits.pdf),
Section 6, develops integer tails for signed polynomials and backward positivity
over suitable gaps. Section 7 uses aggregate tail bounds and positive-tail
counts to prove general algebraic bit sparsity. The paper normalizes its
algebraic input to `(1,2)`. This development works directly with the actual
fractional complement in `(0,1)` and derives its coefficients and boundary
term explicitly. It imports no literature theorem as an assumption and makes
no priority claim.

The stronger eventual square-root count for this algebraic complement is
already supplied by the published general theorem. The remaining formalization
work is to bound the aggregate of the finite suffixes or positive carries in
terms of the complementary one count, and combine that with enough positive
carries forced by the source's gap structure. The present pointwise bound and
local positivity trigger do not yet prove that counting argument.

Normality requires the separate all-block eventual frequency bounds. The
original square-root one-count theorem and logarithmic bounds for both symbols
remain the project's accepted unconditional count estimates at this milestone.
