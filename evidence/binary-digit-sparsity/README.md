# Accepted binary digit sparsity evidence

**Result: accepted.** This packet records a completed full local acceptance run.

- Source commit: [`caa511bd4c4e6697490818fd392b69a62c0dc1c3`](https://github.com/larsbx/golden-ratio-normality-research/commit/caa511bd4c4e6697490818fd392b69a62c0dc1c3).
- Source tree: `31e26b4b0111ba2c159213027c0b4af3b1fb59b0`.
- The checkout was clean. The complete 58-file source inventory and every file's bytes were checked against that exact commit before and after acceptance.
- Upstream proof revision: [`8750345c496390a7ce4f6a80be331451aa999408`](https://github.com/larsbx/finite-math-kernels/commit/8750345c496390a7ce4f6a80be331451aa999408).
- Started (UTC): 2026-11-13T13:32:14.069189+00:00.
- Finished (UTC): 2026-11-13T13:44:34.705541+00:00.
- Lean: Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release).
- Mojo: Mojo 1.1.0.dev2026090805 (34562fa1).
- Full result: [report.json](report.json).
- Transitive assumption audit: [declaration-axioms.json](declaration-axioms.json).
- Printed public types and raw audit: [lean-Audit.json](lean-Audit.json).
- New positive controls: [SparsityCounterexamples.lean](SparsityCounterexamples.lean).
- Exact upstream proof source rebuilt during the run: [BinaryWeight.lean](dependencies/FiniteMathKernels/BinaryWeight.lean).
- Native records: [native/receipts.json](native/receipts.json).
- Generated receipt source: [native/Receipts.lean](native/Receipts.lean).
- Independent receipt types: [ReceiptContracts.lean](ReceiptContracts.lean).

This evidence-only child preserves every accepted application source input.
The report names the source revision used during execution, separately from
the later commit recording this packet. All earlier evidence packets remain
intact. Hosted GitHub Actions and broader upstream repository checks are
separate results; this packet does not claim their success.

## Unconditional mathematical result

For every natural prefix length N, the actual binary one count
s_N = occurrences(2,1,1,N) satisfies

\[
2N \le s_N^2+3s_N+4.
\]

The same bound is proved for the count of [1] in powerDigits 0 N, and for any
finite word with a proved DigitsAt 2 0 binding. The theorem is universal in N;
it does not depend on the native producer's finite execution limits or on an
unproved distribution hypothesis.

The arithmetic proof starts from both inequalities of the prefix certificate
for q=floor(2^N*(phi-1)). Modulo three excludes equality at the polynomial's
lower endpoint. For N>=2, its polynomial evaluation has high-bit quotient
2^(N-2)-1 after division by 2^(N+2). The upstream binary-weight bounds then
give 2N<=W(q)^2+3W(q)+4; the cases N<2 are immediate. Explicit numeral,
alphabet, source-position and count identities transfer this to the actual
digits. Leading zeroes are allowed.

The [derivation](../../docs/binary-digit-sparsity.md) records each step, all
hypotheses, the primary literature attribution, and the scope boundary.
The result forces square-root-scale growth of the one count. It does not
establish limiting frequency one half or any all-block normality estimate.
No priority claim or normality conclusion is made.

## New checks

The application module has nine public theorem statements and three private
bridge lemmas. Seven additional explicit public contract wrappers preserve
their exact types. The imported generic module has twelve explicit arithmetic
theorem statements and one definition; its 25 compiled theorem declarations
include generated helpers.

The new positive control module has **21 explicit theorem statements**.
All **ten new isolated rejection cases** failed for their intended reason:
weight confused with bit length, addition equality despite carries, omitted
binary alphabet, either certificate half used alone, a shifted segment treated
as an origin prefix, deletion of the additive constant, an all-prefix
half-frequency bound, one finite prefix substituted for the universal result,
and a changed arithmetic base. Each returned code 1 with exactly one intended
diagnostic and one error line.

The shifted counterexample is bound to actual power inputs at positions 7, 8, 9,
whose output is [0,0,0]. The first-three-digit example is [1,0,0]. They refute
only those stronger finite claims, not limiting normality.

The **twelve new Python admission methods** test exact dependency and source
identity, including missing/duplicate pins, moving selectors, mismatched
configuration, dirty sources, wrong source roots and revisions, incomplete
source inventories, and modified files hidden from Git status. The gate
fresh-compiles the admitted upstream source and checks the exact source
inventory, file bytes, dependency identities and compiler hash again before
recording acceptance.

## Complete observed acceptance

All **56 Python test methods** passed: 44 inherited and 12 new. The actual native
producers were rebuilt and passed all 10 prefix/count cases, 128 ordinary
automaton inputs, and six power-orbit traces containing 144 input records
through exponent 127. All 17 invalid native requests were rejected. Native
source, execution bounds, fixtures and the BigZ submodule revision are unchanged.
The nine existing Lake pins are unchanged; the additional upstream proof pin
is recorded above and in the report.

All **3,871 inherited receipt theorems** and **1,278 independent exact-type
wrappers** compiled again. All **41 Lean rejection controls** passed, comprising
31 inherited and 10 new controls. All **44 public application contract wrappers**
were printed and audited.

The complete compiled audit inspected **6,190 declarations**, including
**5,732 theorem declarations**, across **25 modules**. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted assumptions. Counts include
generated helpers and finite receipt/type statements; they are not counts of
independent mathematical discoveries.

| Module | Declarations | Theorem declarations |
| --- | ---: | ---: |
| `BridgeCounterexamples` | 6 | 6 |
| `CheckpointCounterexamples` | 39 | 36 |
| `CriteriaCounterexamples` | 17 | 16 |
| `FiniteMathKernels.BinaryWeight` | 26 | 25 |
| `GoldenNormality` | 0 | 0 |
| `GoldenNormality.Automaton` | 237 | 157 |
| `GoldenNormality.BinarySparsity` | 21 | 21 |
| `GoldenNormality.BlockNumerals` | 39 | 28 |
| `GoldenNormality.Blocks` | 61 | 44 |
| `GoldenNormality.Certificates` | 20 | 14 |
| `GoldenNormality.CheckpointBounds` | 15 | 15 |
| `GoldenNormality.Contracts` | 44 | 44 |
| `GoldenNormality.FrequencyBridge` | 16 | 16 |
| `GoldenNormality.Normality` | 5 | 3 |
| `GoldenNormality.NormalityCriteria` | 11 | 9 |
| `GoldenNormality.PowerOrbit` | 41 | 26 |
| `GoldenNormality.Prefix` | 35 | 26 |
| `GoldenNormality.SparseCheckpoints` | 11 | 9 |
| `GoldenNormality.SquareCheckpoints` | 14 | 12 |
| `GoldenNormality.WordEncoding` | 21 | 15 |
| `GoldenNormality.ZeckendorfEncoding` | 35 | 28 |
| `PowerOrbitCounterexamples` | 12 | 12 |
| `ReceiptContracts` | 1278 | 1278 |
| `Receipts` | 4165 | 3871 |
| `SparsityCounterexamples` | 21 | 21 |

## Replay and integrity

After checking out the exact source revision and installing its pinned
dependencies, run:

```sh
python3 tools/verify.py --output build/replay-binary-sparsity
```

Use a clean committed checkout and a fresh output directory. The gate uses
fresh project and upstream proof objects. Native tools run with telemetry and
crash reporting disabled, without activation hooks; temporary compiler files
are cleaned automatically.

All **158 hashed artifacts** are preserved at their report-relative
paths, alongside the unchanged report and this summary. Native binaries and
proof objects are rebuilt during replay; executable identities are recorded
in the report. The copied upstream proof source hash is
`47bc675ccb9b01094074ab3fb989e1dc6d0abb9b8a86aa751df97cc400f38614`.

The all-block eventual frequency estimates remain open. The new one-count
bound supplies neither those estimates nor a universal native implementation
or compiler refinement theorem.
