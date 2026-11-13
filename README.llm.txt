GOLDEN RATIO NORMALITY RESEARCH: WORKING CONTRACT

Goal
Build mechanically checked infrastructure for research on normality of
phi=(1+sqrt(5))/2 in integer bases. The first milestone is an exact finite
foundation. A proof of normality is not an output of this milestone.

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
Count consecutive windows, allowing overlaps. N starting positions require
N+k-1 digits for k>=1. Empty patterns have count zero in the list API and
are excluded from the normality target.
Fibonacci words are read most significant first, with least significant
weight F_2=1 followed by F_3=2. Adjacent ones are rejected; leading zeros
are allowed. The automaton input for binary digit n must represent 2^n.

Implementation boundary
kernel/ is canonical Mojo. It imports arbitrary-precision arithmetic from
the exact vendor/finite-math-kernels submodule revision. Do not fork BigZ
locally. oracles/ uses an independently written integer-square-root method
and slice-based counting. tools/ converts checked native receipts into
closed Lean propositions; the Lean kernel checks those propositions.

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
