GOLDEN RATIO NORMALITY RESEARCH: WORKING CONTRACT

Goal
Build mechanically checked infrastructure for research on normality of
phi=(1+sqrt(5))/2 in integer bases. The exact finite foundation now connects
certified word counts to the occurrences function in NormalInBase. Equivalent
word/count targets and a conditional checkpoint criterion now preserve the
remaining quantifiers. These milestones establish no unconditional normality result.

Authority and scope
1. Universal Lean theorems are accepted only after compilation of the exact
   source and inspection of their compiled types and transitive axioms.
2. Closed Lean certificates concern the supplied finite objects only.
3. Native Mojo/Python agreement is finite conformance evidence. It is not a
   universal compiler, BigZ, or native implementation refinement proof.
4. Published results are attributed, with hypotheses retained. The binary
   eight-state Fibonacci-input automaton is prior art, not a new discovery.
5. Open statements remain definitions or explicit research obligations. Do
   not introduce an axiom, sorry, or native_decide to make them compile.

Conventions
alpha=phi-1; digit positions begin at zero after the radix point.
q_n=floor(b^n*alpha); d_n=q_(n+1)-b*q_n.
A k-block beginning at n has value q_(n+k)-b^k*q_n, including leading zeros.
Count consecutive windows, allowing overlaps. A prefix of N+k-1 digits
gives N complete starting positions for k>=1. Empty patterns have count zero
in the list API and are excluded from the normality target.
The universal count bridge uses N=L+1-k in truncated natural arithmetic,
so every L<k yields zero starts. Word values are injective only with equal
lengths and alphabet bounds. A leading zero must not erase the block width.
wordOfValue covers every j<b^k uniquely, including k=0,j=0. Its alphabet and
value-recovery contracts require the stated bound; raw out-of-range inputs
are not valid block encodings.
NormalByWords is equivalent to NormalInBase with all eventual quantifiers.
UniformBlockNormality permits one N0 for all j of a fixed k and T. Neither
k nor T may be moved after that existential threshold.
Fibonacci words are read most significant first, with least significant
weight F_2=1 followed by F_3=2. Adjacent ones are rejected; leading zeros
are allowed. The automaton input for binary digit n must represent 2^n.

Implementation boundary
kernel/ is canonical Mojo. It imports arbitrary-precision arithmetic from
the exact vendor/finite-math-kernels submodule revision. Do not fork BigZ
locally. oracles/ uses an independently written integer-square-root method
and slice-based counting. tools/ converts checked native receipts into
closed Lean propositions; the Lean kernel checks those propositions.
Each pattern receipt includes the exact occurrences count and Nat.dist
discrepancy used by NormalInBase. These are finite equalities, without an
eventual bound or any claim of uniform convergence.
Configured interval receipts bind two actual prefixes to the same base and
pattern. For L<=N<=R they use D(N)<=max(D(L),D(R))+(R-L). The gap term cannot
be deleted. The normality implication additionally requires a strictly
increasing sequence on all natural indices and budgets at every sufficiently
late interval, separately for every valid k,j,T. Finite cases supply none of
those infinite hypotheses; a constant sequence q=0 is an explicit vacuity control.

Acceptance
Run python3 tools/verify.py after installing pinned dependencies. Missing
tools, timeouts, malformed output, changed sources during a run, failed
negative controls, or unexpected axioms are failures. Reports under build/
describe that run, with source hashes and toolchain identities. A committed
evidence report must identify the exact source revision it checked; an
evidence-only child commit does not change that source revision.

Open mathematical gap
The published automaton evaluates a digit predicate on every admissible
Fibonacci word. Normality concerns the particular sparse input sequence
Z(b^n), and all output block frequencies, with quantifiers uniform in the
required way. Distribution over all words, finite prefixes, or a stationary
distribution of an unrelated chain does not fill this gap. Read
docs/literature-gate.md before proposing a new universal invariant.
