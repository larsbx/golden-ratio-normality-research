# Accepted sparse-checkpoint evidence

**Result: accepted.** This packet records a completed local acceptance run.

- Source commit: [`86c5d28fb4377d7bf5ff4173be25403cdbeffc6d`](https://github.com/larsbx/golden-ratio-normality-research/commit/86c5d28fb4377d7bf5ff4173be25403cdbeffc6d).
- Source tree: `dbd26fc5f3a1043a938694a4830f0baf03a5f3df`.
- The source checkout was clean. All 53 source hashes and all dependency revisions were checked again before acceptance.
- Started (UTC): 2026-11-13T11:31:24.617909+00:00.
- Finished (UTC): 2026-11-13T12:31:08.310632+00:00.
- Lean: Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release).
- Mojo: Mojo 1.1.0.dev2026090805 (34562fa1).
- Full result: [report.json](report.json).
- Transitive assumption audit: [declaration-axioms.json](declaration-axioms.json).
- Printed public types and complete audit: [lean-Audit.json](lean-Audit.json).
- New positive controls: [CheckpointCounterexamples.lean](CheckpointCounterexamples.lean).
- Native records: [native/receipts.json](native/receipts.json).
- Generated receipt source: [native/Receipts.lean](native/Receipts.lean).
- Independent exact types: [ReceiptContracts.lean](ReceiptContracts.lean).

This evidence-only child preserves the accepted source files. The report names
the source revision used during execution, separately from the later commit
recording this packet. All earlier evidence packets remain intact.

## New mathematical contracts

Two new project modules prove the endpoint and square-checkpoint criteria.
The separate endpoint bounds at tolerance 4T and relative-gap bound at 4T
imply the existing interval budget at tolerance T, retaining the different
normalizations at L and R. A strictly increasing sequence with vanishing
relative gaps gives an endpoint-only target equivalent to NormalInBase.

Squares discharge the geometric hypothesis: their exact gap is 2i+1, and
i>=3T suffices for the T-gap bound. At i>=12T, bounds at the two square
endpoints with tolerance 4T control every intermediate N with tolerance T.
These thresholds control geometry; they supply no golden-ratio frequency
estimate.

The binary square target counts every block start in the whole origin prefix
of length i^2+word.length-1. It retains every nonempty binary word, positive
tolerance, positive eventual index threshold, and every subsequent index.
Lean proves its equivalence to NormalInBase 2.

All seven new explicit public contract wrappers compiled. The new positive
control module contains **24 explicitly stated control theorems** and 12 generated
proof helpers, for 36 compiled theorem declarations. Its abstract count family
has increments in {0,1} and is balanced at 2M and 4M, while its discrepancy
at 3M is M for every M>=1. This concerns one abstract count and a finite
interval at each scale, not an all-block or golden-ratio counterexample.

The **eight new rejection controls** all failed for their intended reason:
premature square-gap threshold, geometric relative gap, constant-zero growth,
gap-free single-count interpolation, truncated square window, weakened finite
interval type, weakened all-late checkpoint quantifier, and weakened binary
square equivalence. Each isolated control exited with code 1, one intended
diagnostic, and exactly one error line.

The [derivation](../../docs/sparse-checkpoints.md) records the complete
quantifiers, elementary proof, source conventions, counterexamples, and
literature boundary. Vanishing relative gaps are sufficient for the elementary
route proved here; they are not asserted necessary for all normality criteria.
The stronger published Piatetski-Shapiro criterion is neither imported nor
claimed as a formal result of this development.

## Complete observed acceptance

The full gate passed all **44 inherited Python test methods** and rebuilt the
actual native producers. It passed all 10 prefix/count cases, 128 ordinary
automaton inputs, and six power-orbit traces. Those traces contain 144 input
records through exponent 127, including nonzero starts 17 and 64. All 17
invalid native requests were rejected. This milestone changes no native
producer, execution bound, finite fixture, or dependency pin.

All **3,871 inherited receipt theorems** and **1,278 independent exact-type
wrappers** compiled again. The gate retains all earlier occurrence,
discrepancy, interval, power-source, digit, and count statements. No additional
finite prefix length or actual golden-ratio distribution bound is claimed.

All **31 Lean rejection controls** passed: the 23 inherited controls and eight
new controls. The complete compiled audit inspected **6,115
declarations**, including **5,658 theorem declarations**, in **22 modules**.
All **37 explicit public contract wrappers** were printed and audited. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted assumptions.
The declaration totals include generated helpers and finite receipt/type
statements; they are not counts of independent mathematical results.

| Module | Declarations | Theorem declarations |
| --- | ---: | ---: |
| `BridgeCounterexamples` | 6 | 6 |
| `CheckpointCounterexamples` | 39 | 36 |
| `CriteriaCounterexamples` | 17 | 16 |
| `GoldenNormality` | 0 | 0 |
| `GoldenNormality.Automaton` | 237 | 157 |
| `GoldenNormality.BlockNumerals` | 39 | 28 |
| `GoldenNormality.Blocks` | 61 | 44 |
| `GoldenNormality.Certificates` | 20 | 14 |
| `GoldenNormality.CheckpointBounds` | 15 | 15 |
| `GoldenNormality.Contracts` | 37 | 37 |
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

## Replay and integrity

After installing the repository's pinned dependencies, run:

```sh
python3 tools/verify.py --output build/replay-sparse-checkpoints
```

Use a fresh output directory. The gate uses fresh project proof objects and
invokes the installed native tools with telemetry and crash reporting disabled,
without activation hooks. Native compiler scratch files use automatically
cleaned temporary directories on the project volume.

All **133 artifacts** listed in artifact_sha256 are included at
their exact relative paths and with matching hashes, alongside the unchanged
report and this summary. Native binaries and project proof objects are rebuilt
during replay; executable identities are recorded in the report. Hosted GitHub
Actions acceptance is a separate result and is not asserted by this packet.

## Remaining obligation

The eventual endpoint-frequency bound for the actual golden-ratio power orbit
at square numbers of starts remains open, separately for every nonempty binary
word and every positive tolerance. No unconditional normality result, native
implementation refinement theorem, or compiler correctness theorem follows
from this evidence packet.
