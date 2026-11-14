# Accepted binary power-orbit evidence

**Result: accepted.** This packet records a completed local acceptance run.

- Source commit: [`f5d6e4ea7a3fcf5321587f89329cd913097fa9ae`](https://github.com/larsbx/golden-ratio-normality-research/commit/f5d6e4ea7a3fcf5321587f89329cd913097fa9ae).
- Source tree: `ef19c312a91b61aca14f05dc3607da29a8d14b61`.
- The source checkout was clean. All 49 source hashes and all dependency revisions were checked again before acceptance.
- Started (UTC): 2026-11-13T10:12:11.265647+00:00.
- Finished (UTC): 2026-11-13T10:20:08.869313+00:00.
- Lean: Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release).
- Mojo: Mojo 1.1.0.dev2026090805 (34562fa1).
- Full result: [report.json](report.json).
- Transitive assumption audit: [declaration-axioms.json](declaration-axioms.json).
- Native records: [native/receipts.json](native/receipts.json).
- Generated theorem source: [native/Receipts.lean](native/Receipts.lean).
- Independent exact types: [ReceiptContracts.lean](ReceiptContracts.lean).
- Power-orbit counterexamples: [PowerOrbitCounterexamples.lean](PowerOrbitCounterexamples.lean).
- Printed public types and complete audit: [lean-Audit.json](lean-Audit.json).

This evidence-only child preserves the accepted source files. The report names
the source revision used during execution, separately from the later commit
recording this packet. All earlier evidence packets remain intact.

## Observed acceptance

All **44 Python test methods** passed. Actual native execution passed all
10 prefix/count cases, 128 ordinary automaton inputs, and six power-orbit cases.
All **17 invalid native requests** were rejected with their required diagnostic:
eight inherited requests and nine power-orbit requests, including exact
INT64_MAX as a start with length one.

The power-orbit cases contain **144 input records**, including powers from
2^0 through 2^127, empty/short prefixes, and nonzero starts 17 and 64.
The primary 128-digit width-three histogram is `[16,15,9,18,16,12,18,22]`,
with 126 complete starts. Powers stay in the pinned upstream BigZ type.
The native dependency revision is `3573dc4318f4d5ccd6a103b470dc82bed1f798a8`.

Lean compiled **3,871 required receipt theorems**, including the 3,237 inherited
receipts and **634 new power-orbit theorems**:

- 432 individual power-value, classifier-output, and actual-digit statements.
- 18 trace bindings, actual-digit word bindings, and canonical-output equalities.
- 120 list, actual-segment, and canonical-segment count statements.
- 64 origin-only occurrence and discrepancy statements.

The independent wrapper module checked **1,278 exact types**. Every one of the
634 new power-orbit receipts receives a wrapper, with expected positions,
digits, counts, and start expressions computed from the fixed contract and
root/slice oracle rather than the native record or its translator.

All **23 Lean rejection controls** passed: 16 inherited controls and seven
power-orbit controls. The new controls reject a valid classifier input bound
to the wrong power, a shifted power position, unequal trace lengths, an
incorrect output, ordinary integer inputs used in place of powers, a shifted
segment presented as an origin prefix, and a one-way implication supplied
where the normality equivalence is required. Every isolated semantic control
failed with exactly one intended diagnostic and one error line.

The compiled audit inspected **6,044 declarations** in **19 modules**,
including **5,594 theorem declarations** and all **30 explicit public
contract wrappers**. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted assumptions. These counts include generated helpers and finite
receipt/type statements; they are not counts of independent new results.

| Module | Declarations | Theorem declarations |
| --- | ---: | ---: |
| `BridgeCounterexamples` | 6 | 6 |
| `CriteriaCounterexamples` | 17 | 16 |
| `GoldenNormality` | 0 | 0 |
| `GoldenNormality.Automaton` | 237 | 157 |
| `GoldenNormality.BlockNumerals` | 39 | 28 |
| `GoldenNormality.Blocks` | 61 | 44 |
| `GoldenNormality.Certificates` | 20 | 14 |
| `GoldenNormality.CheckpointBounds` | 15 | 15 |
| `GoldenNormality.Contracts` | 30 | 30 |
| `GoldenNormality.FrequencyBridge` | 16 | 16 |
| `GoldenNormality.Normality` | 5 | 3 |
| `GoldenNormality.NormalityCriteria` | 11 | 9 |
| `GoldenNormality.PowerOrbit` | 41 | 26 |
| `GoldenNormality.Prefix` | 35 | 26 |
| `GoldenNormality.WordEncoding` | 21 | 15 |
| `GoldenNormality.ZeckendorfEncoding` | 35 | 28 |
| `PowerOrbitCounterexamples` | 12 | 12 |
| `ReceiptContracts` | 1278 | 1278 |
| `Receipts` | 4165 | 3871 |

## Exact mathematical scope

The total Lean encoder converts pinned mathlib Zeckendorf index lists into
admissible Boolean words with exact Fibonacci value, for every natural input.
The automaton's total evaluator is therefore always accepted, and its outputs
on 2^n equal the actual binary fractional digits at zero-based position n.
Every computable output segment equals the actual segment at its same start
and length; every nonempty binary word has the corresponding exact overlapping
count. The complete eventual count condition on these computable words is
proved equivalent to `NormalInBase 2`.

Finite `PowerOrbitAt` witnesses separately retain every supplied input's power
value, classifier output, source offset, and matching trace length. Their input
representations may contain leading zeros and need not equal the canonical
Lean encoding. Their output words agree through the shared actual-digit
semantics, so the receipt path does not need to reduce the reference encoder
at large powers.

The shifted fixtures keep source 17/length 8 and source 64/length 4 throughout
the exact-type checks. They receive segment counts only. The first-N
occurrence theorem explicitly requires a trace beginning at zero.

The [derivation](../../docs/power-orbit.md) records the quantifiers, source
contracts, counterexamples, and prior-art attribution. This packet establishes
neither an eventual golden-ratio discrepancy estimate nor unconditional
normality. It also supplies no universal refinement theorem for the native
encoder, BigZ implementation, or compiler, and no efficiency claim for the
reference Lean encoder.

## Replay and integrity

After installing the repository's pinned dependencies, run:

```sh
python3 tools/verify.py --output build/replay-power-orbit
```

Use a fresh output directory. The gate invokes actual installed native tools
with telemetry and crash reporting disabled, without activation hooks. Native
compiler scratch space uses a temporary directory on the project volume and
is removed after compilation.

All **113 artifacts** listed in `artifact_sha256` are included at
their exact relative paths and with matching hashes, alongside the unchanged
report and this summary. Native binaries and project proof objects are rebuilt
during replay; executable identities are recorded in the report. Hosted GitHub
Actions acceptance is a separate result and is not asserted by this packet.
