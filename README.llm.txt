GOLDEN RATIO NORMALITY RESEARCH: WORKING CONTRACT

Goal
Build mechanically checked infrastructure for research on normality of
phi=(1+sqrt(5))/2 in integer bases. The exact finite foundation now connects
certified word counts to the occurrences function in NormalInBase. Equivalent
word/count targets and a conditional checkpoint criterion now preserve the
remaining quantifiers. These milestones establish no unconditional normality result.
The binary power orbit now has a total computable Lean encoder/evaluator, with
proved word and count identities and an equivalent explicit normality target.
Normality is now also equivalent to its endpoint estimates along any strictly
increasing checkpoint sequence with vanishing relative gaps. Squares discharge
that geometric condition, giving a fully quantified sparse power-orbit target.
An unconditional binary sparsity theorem now proves 2N<=s_N^2+3s_N+4 for
the actual one count at every prefix length N. This supplies square-root-scale
growth, not the limiting frequency one half or an all-block estimate.
Binary run bounds now apply at every start n: any constant segment has length
at most n+1, so [n,2n+2) contains both symbols. For d<2, every origin prefix of
length N>=2^(m+1)-2 contains at least m copies of d. This logarithmic bound
adds zero recurrence; it does not strengthen the existing one-count sparsity.

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
The sparse-checkpoint gate compiles two additional project modules, seven
explicit contract wrappers, and positive/negative controls. It retains every
native fixture and finite receipt without changing producer code or pins.
Native compilation uses automatically cleaned scratch space under ignored build/,
without relying on capacity in the shared temporary filesystem.

Open mathematical gap
The published automaton evaluates a digit predicate on every admissible
Fibonacci word. Normality concerns the particular sparse input sequence
Z(b^n), and all output block frequencies, with quantifiers uniform in the
required way. Distribution over all words, finite prefixes, or a stationary
distribution of an unrelated chain does not fill this gap. Read
docs/literature-gate.md before proposing a new universal invariant.

Sparse checkpoint contract
NormalOnCheckpoints b q fixes q before every k,j,T and requires a bound at
every index beyond a threshold depending on k,j,T. It includes b>=2, but
does not hide any growth condition. StrictMono q and VanishingRelativeGaps q
are separate hypotheses of the equivalence. The latter means that for every
T>=1, eventually (q(i+1)-q i)*T<=q i. Constant zero satisfies the two numerical
predicates vacuously and is rejected by the growth requirement.
Independent endpoint bounds D(L)*(4T)<=L and D(R)*(4T)<=R, together with
(R-L)*(4T)<=L, imply the existing full interval budget at T. Retain the
different endpoint denominators and the interval coverage hypotheses.
squareCheckpoint i=i^2 has exact gap2i+1; i>=3T suffices for its T-gap bound.
The finite square interval corollary needs i>=12T and endpoint bounds at4T.
This explicit index controls geometry only, not when phi's frequency estimate
holds. PowerOrbitSquareNormality retains every nonempty binary word, T>=1,
positive eventual index, and every later index. Its count uses the whole prefix
of length i^2+word.length-1, not only i^2 digits or digits sampled at squares.
The geometric-checkpoint/sawtooth controls concern one abstract count. They
must not be described as a counterexample to ALL-block convergence at bounded
ratio checkpoints: the published Piatetski-Shapiro criterion gives another
route there. No formalization of that stronger theorem is imported or claimed.

Binary sparsity contract
FiniteMathKernels.binaryWeight q is the sum of Nat.digits 2 q, not the bit length
or the numeral q. Reusable carry, shift, quotient, all-ones and triangular
square-weight lemmas live upstream in finite-math-kernels. A separate exact
Lake Git pin imports tests/lean; the native BigZ submodule revision is unchanged.
The acceptance gate compares the proof bytes with their pinned Git blob,
fresh-compiles and audits the module, retains the source copy, and rechecks the
pin and hash at the end. Never edit vendor files or create a competing local
binary-weight implementation.
For PrefixCertificate (2^N) q, the polynomial cannot equal (2^N)^2 modulo3.
For N>=2 its quotient by2^(N+2) is exactly2^(N-2)-1. Both certificate halves,
base2, and the N>=2 hypothesis of this quotient theorem must be retained.
Combining the high-bit block with 2*W(q^2)<=W(q)*(W(q)+1) proves
2N<=W(q)^2+3W(q)+4 for everyN, with N<2 handled separately.
Numeral weight equals the count of [1] only for a binary alphabet word;
leading zeroes are allowed. The evaluator's origin prefix satisfies the root
certificate. The final bound uses occurrences2 1 1 N or the whole powerDigits0N
word, and certified transfer requires DigitsAt2 0. It does not apply to arbitrary
shifted segments. The actual shifted three-zero control and first3bits100
counterexample refute only those overstated finite variants, not normality.
The method is attributed to Bailey--Borwein--Crandall--Pomerance. No novelty or
universal native implementation refinement is claimed. Read the derivation and
scope in docs/binary-digit-sparsity.md before extending this result.

Binary run and recurrence contract
For start n,length k,B=2^n,D=2^k, keep BOTH exact prefix certificates at n and
n+k. A zero run means Q=D*q; a one run means Q+1=D*(q+1). The positive integer
residual at the first endpoint scales by D^2 and is bounded by <3*B*D at the
second endpoint. A run of k>=n+2 is impossible. The actual word bridge retains
base2, starting position, and length. Empty runs are allowed by the bound.
For any d<2, powerDigits n (n+2) contains d; the equivalent witness satisfies
n<=i<2*n+2 with an EXCLUSIVE upper endpoint. Do not shorten to n+1 or reset
a shifted source to zero. Actual00 at n=1 and1111 at n=3 refute both changes.
Recurrence checkpoints a_m=2^(m+1)-2 have a_0=0 and a_(m+1)=2*a_m+2.
Their disjoint windows each supply a zero and a one, giving count>=m for
every N>=a_m and d<2. Preserve the binary-symbol bound and origin-prefix
count convention. Infinite recurrence does not imply normality, positive
density, bounded gaps, or occurrence of every longer word.
The complementary beta=1-alpha has beta^2-3beta+1=0. The negative coefficient
prevents direct reuse of the positive-polynomial proof. BBCP Theorem7.1
already gives an eventual sqrt-scale bound in the literature; the open item
is this project's source-bound complement and signed-tail formalization,
not a newly unresolved mathematical existence claim. See the run derivation
and literature check in docs/binary-runs-and-recurrence.md.
