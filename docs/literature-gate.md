# Foundation literature gate

Decision: proceed with exact extraction, contiguous counting, and a verified
binary automaton. No normality theorem is assumed or claimed.

## Sources inspected

1. A. Barnoff, C. Bright, J. Shallit, *Computing the base-b representation of
   quadratic irrationals using automata*, Theoretical Computer Science 1071
   (2026), 115843. https://doi.org/10.1016/j.tcs.2026.115843
   Author manuscript: https://cs.uwaterloo.ca/~cbright/reports/digits-automata.pdf
   Theorem 1 and Figure 2 provide the arithmetic meaning and eight-state binary
   automaton. Its input is the Zeckendorf representation of b^n, not the base-b
   representation of n. Some smaller SAT-fitted machines for other quadratics
   remain conjectural; they are not used here.
2. B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers I.
   Expansions in integer bases*, Annals of Mathematics 165 (2007), 547–565.
   https://annals.math.princeton.edu/2007/165-2/p04
   An algebraic irrational's block complexity divided by block length tends
   to infinity. The Fibonacci substitution word cannot be identified with
   phi's ordinary base-b digit sequence.
3. A. Kozachinskiy, A. Shen, *Automatic Kolmogorov complexity, normality, and
   finite state dimension revisited*, arXiv:1701.09060v6, section 4.2.
   https://arxiv.org/abs/1701.09060
   A single constant bounding every block's upper frequency by C*b^(-k)
   suffices for normality. A separate unrestricted C_k is insufficient.
4. Y. Kanado, K. Saito, *Normality of algebraic numbers and the Riemann zeta
   function*, arXiv:2412.02337v2.
   https://arxiv.org/abs/2412.02337
   Records the open algebraic-normality problem and gives an analytic
   reformulation, not an estimate settling phi.
5. D. H. Bailey, J. M. Borwein, R. E. Crandall, C. Pomerance,
   *On the binary expansions of algebraic numbers*.
   Author PDF: https://www.davidhbailey.com/dhbpapers/algebraic-bits.pdf
   Lemma 4.1 and Theorem 4.2 provide binary-weight estimates. Theorem 5.2 uses
   polynomial truncation and high one bits; its golden-mean specialization
   appears after Corollary 5.3. The result concerns sparsity, not normality.

## Scope of this work

The root certificate is an elementary polynomial/floor argument. The published
automaton is prior art. This project adds machine-checked application proofs
and reproducible native certificate checks; it does not claim either object
as a new mathematical discovery.

The unresolved normality obligation is a uniform frequency statement for
the particular inputs Z(b^n). Counting all integers or all admissible
Fibonacci strings cannot replace counting those inputs: evenness has density
one half on integers but holds on every 2^n for n >= 1.

The current target is ordinary integer-base normality. Pisot estimates for
phi^n and canonical/greedy representation languages address different claims.

## Sparse checkpoint follow-up

The endpoint interpolation development uses elementary monotonicity and exact
integer budgets. It proves a sufficient vanishing-relative-gap condition and
discharges that geometry for square checkpoints; it claims no new distribution
estimate or novelty for the interpolation method.

The primary-source check revisited Kozachinskiy--Shen, section 4.2, before
designing the sparse-checkpoint controls. A geometric sequence fails the
vanishing-relative-gap hypothesis used here, and one block can have large
intermediate deviations despite balanced endpoints. Neither fact refutes an
ALL-block criterion at bounded-ratio checkpoints: the published common-constant
upper-frequency criterion permits a different route. The code does not import
or claim a formal proof of that stronger criterion. See
[the sparse checkpoint derivation](sparse-checkpoints.md) for the exact scope.

## Binary digit sparsity follow-up

The primary-source check inspected the weight estimates, polynomial truncation
argument, and explicit golden-mean specialization before formalization. The
application now proves `2N<=s_N^2+3s_N+4` for every actual binary origin-prefix
one count. Its reusable arithmetic lemmas live upstream; its certificate and
source-count transfer live here. The finite coefficient uses the elementary
triangular square-weight estimate, separately proved by binary induction.
The paper supplies context and attribution, not a Lean axiom. No priority
claim is made for this specialization or refinement. See
[the exact derivation](binary-digit-sparsity.md) for hypotheses and limits.

## Binary run and recurrence follow-up

The primary-source check revisited Bailey--Borwein--Crandall--Pomerance
Sections 3, 5, and 7. Section 3 obtains an eventual gap and logarithmic count
bound from Roth's theorem. The application now supplies an elementary,
all-start quadratic bound from integer residuals: every run starting at n has
length at most n+1, and each symbol occurs at least m times by prefix length
2^(m+1)-2. This is an explicit formalization, with no priority claim.

The sign restriction of Theorem 5.2 is essential. For the complement 1-alpha,
the polynomial x^2-3x+1 has a negative linear coefficient; substituting its
prefix into the existing positive-polynomial proof is invalid. The general
Theorem 7.1 supplies a stronger eventual square-root lower count in the
literature, but its signed-tail argument and the source-bound complement
bridge remain unformalized here. The new run proof does not invoke Roth or
import a literature theorem as an axiom. See
[the run and recurrence derivation](binary-runs-and-recurrence.md).
