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
