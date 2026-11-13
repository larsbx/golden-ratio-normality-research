GOLDEN RATIO NORMALITY RESEARCH: WORKING CONTRACT

Goal
Build mechanically checked infrastructure for research on normality of
phi=(1+sqrt(5))/2 in integer bases. The exact finite foundation now connects
certified word counts to the occurrences function in NormalInBase. Equivalent
word/count targets and a conditional checkpoint criterion now preserve the
remaining quantifiers. These milestones establish no unconditional normality result.
The binary power orbit now has a total computable Lean encoder/evaluator, with
proved word and count identities and an equivalent explicit normality target.

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
BinaryAutomaton.encode converts pinned mathlib's Zeckendorf index list into
the Bool-word format, proving admissibility and exact Fibonacci value for all q.
evaluated uses classify(encode q); its fallback is proved unreachable.
powerDigit n=evaluated(2^n), and powerDigits retains both start and length.
PowerOrbitNormality is equivalent to NormalInBase 2, with every nonempty binary
word, positive tolerance, positive eventual threshold, and subsequent N retained.

Implementation boundary
kernel/ is canonical Mojo. It imports arbitrary-precision arithmetic from
the exact vendor/finite-math-kernels submodule revision. Do not fork BigZ
locally. oracles/ uses an independently written integer-square-root method
and slice-based counting. tools/ converts checked native receipts into
closed Lean propositions; the Lean kernel checks those propositions.
Each origin-prefix pattern receipt includes the exact occurrences count and Nat.dist
discrepancy used by NormalInBase. These are finite equalities, without an
eventual bound or any claim of uniform convergence.
Configured interval receipts bind two actual prefixes to the same base and
pattern. For L<=N<=R they use D(N)<=max(D(L),D(R))+(R-L). The gap term cannot
be deleted. The normality implication additionally requires a strictly
increasing sequence on all natural indices and budgets at every sufficiently
late interval, separately for every valid k,j,T. Finite cases supply none of
those infinite hypotheses; a constant sequence q=0 is an explicit vacuity control.
PowerOrbitAt start inputs outputs is a separate finite witness relation. Every
input must represent 2^(start+offset), classify to the supplied output, and match
the output list length. Leading zeros are allowed; equality to canonical encode
is not required. The relation proves DigitsAt and equality to powerDigits, using
symbolic proofs rather than reducing the reference encoder at large powers.
Only traces beginning at zero may supply first-N occurrences. Nonzero-start
traces supply actual/canonical segment counts and keep their original start.
kernel/power_orbit.mojo uses upstream BigZ doubling. Its explicit execution
bounds are start 0..4096, length 0..256, end<=4096, width1..4, base2. Bound
machine metadata operands before addition. The strict oracle binds every input
exponent, canonical decimal power, Fibonacci representation, classifier output,
whole digit segment, and histogram. Fibonacci text has the native 10,000-symbol
budget; leading-zero padding inside the budget remains valid.
Do not claim universal native encoder refinement: the Lean total encoder is
proved independently and each emitted native witness is checked on its own.

Acceptance
Run python3 tools/verify.py after installing pinned dependencies. Missing
tools, timeouts, malformed output, changed sources during a run, failed
negative controls, or unexpected axioms are failures. Reports under build/
describe that run, with source hashes and toolchain identities. A committed
evidence report must identify the exact source revision it checked; an
evidence-only child commit does not change that source revision.
The full gate builds the actual power-orbit executable, checks every configured
trace and invalid request, compiles all emitted power receipts, and independently
fixes every new receipt type from the contract and root/slice oracle. Positive
controls retain leading-zero words and shifted source segments. Negative controls
reject valid classifier inputs with wrong power values, wrong positions, unequal
trace lengths, wrong outputs, ordinal inputs substituted for powers, shifted
sources presented as prefixes, and one-way implications substituted for iff types.
Native compilation uses automatically cleaned scratch space under ignored build/,
without relying on capacity in the shared temporary filesystem.

Open mathematical gap
The published automaton evaluates a digit predicate on every admissible
Fibonacci word. Normality concerns the particular sparse input sequence
Z(b^n), and all output block frequencies, with quantifiers uniform in the
required way. Distribution over all words, finite prefixes, or a stationary
distribution of an unrelated chain does not fill this gap. Read
docs/literature-gate.md before proposing a new universal invariant.
