# Accepted block-frequency bridge evidence

**Result: accepted.** This packet records a completed local acceptance run.

- Source commit: [`1c7314c7544eabde6da9cc9d70eada7c10ca95ae`](https://github.com/larsbx/golden-ratio-normality-research/commit/1c7314c7544eabde6da9cc9d70eada7c10ca95ae).
- Source tree: `0e49a5ddedb68476442f569976c4224e8552d49e`.
- The source checkout was clean at the start. Project source hashes and all dependency revisions were checked again before acceptance.
- Started (UTC): 2026-11-13T08:38:43.373133+00:00.
- Finished (UTC): 2026-11-13T08:42:30.631600+00:00.
- Lean: Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release).
- Mojo: Mojo 1.1.0.dev2026090805 (34562fa1).
- Full result: [report.json](report.json).
- Compiled dependency audit: [declaration-axioms.json](declaration-axioms.json).
- Native records: [native/receipts.json](native/receipts.json).
- Generated finite theorems: [native/Receipts.lean](native/Receipts.lean).
- Independently generated exact receipt types: [ReceiptContracts.lean](ReceiptContracts.lean).
- Compiled semantic counterexamples: [BridgeCounterexamples.lean](BridgeCounterexamples.lean).
- Public theorem types and complete audit output: [lean-Audit.json](lean-Audit.json).

This evidence-only child preserves the accepted source files. The report names
the source revision that existed during the run, separately from the later
commit that records its evidence. The earlier foundation packet remains intact.

## Observed checks

All 25 Python test methods passed. Actual Mojo producers agreed with the
independent oracle on all **nine prefix/count cases** and all **128 Fibonacci
inputs**. All **eight invalid native requests** were rejected with their required
diagnostics. The prefix cases include empty and nonempty words shorter than
the block, and the binary word `100` with exactly one complete length-three start.

The generated receipt module contains exactly **2,747 required theorem
declarations**: 558 prefix certificates, 549 digit equalities, 9 whole-word
bindings, 310 computational counts, 310 actual-digit counts, 310 occurrence
equalities, 310 exact discrepancy equalities, 128 triples of Fibonacci-value,
classification, and arithmetic-output facts, and 7 power-input digit facts.

A separate module verifies **620 exact receipt types** using expected counts
recomputed directly from the fixed contract and the independent sqrt/slice
oracle. Both the complete-start expression and the discrepancy right-hand side
are evaluated in Lean. These wrappers prevent a terminal receipt weakened to
`True` from satisfying the acceptance gate merely by retaining its name.

All **11 Lean rejection controls** passed: the six inherited controls for false
root, scattered count, invalid Fibonacci word, weakened theorem type, a direct
added assumption, and an assumption inherited through an imported theorem;
plus unequal encoding lengths, a symbol outside the alphabet, empty-pattern
transfer, an extra start in a short prefix, and a weakened discrepancy receipt.
Each new control emitted exactly its one intended error.

The compiled audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
It inspected every declaration in the following modules, including helpers
created by Lean. These counts are not counts of independent new mathematical
results; the 620 receipt contracts independently check the original receipts.

| Compiled module | Declarations | Theorem declarations |
| --- | ---: | ---: |
| `BridgeCounterexamples` | 6 | 6 |
| `GoldenNormality` | 0 | 0 |
| `GoldenNormality.Automaton` | 237 | 157 |
| `GoldenNormality.BlockNumerals` | 39 | 28 |
| `GoldenNormality.Blocks` | 61 | 44 |
| `GoldenNormality.Certificates` | 20 | 14 |
| `GoldenNormality.Contracts` | 14 | 14 |
| `GoldenNormality.FrequencyBridge` | 16 | 16 |
| `GoldenNormality.Normality` | 5 | 3 |
| `GoldenNormality.Prefix` | 35 | 26 |
| `ReceiptContracts` | 620 | 620 |
| `Receipts` | 2884 | 2747 |

## Scope and replay

The new universal theorem identifies a nonempty alphabet pattern's overlapping
count in the actual first L digits with `occurrences` over `max(0,L+1-k)` starts,
for every base at least two. Its certificate and discrepancy corollaries retain
the exact prefix binding, block width, base, and finite start count. Leading
zeros remain part of the fixed-length word.

The [derivation](../../docs/block-frequency-bridge.md) explains the hypotheses,
counterexamples, and the remaining eventual frequency bound. This packet
supplies no normality theorem, asymptotic estimate, or universal refinement
proof for native execution or either compiler.

Install the pinned dependencies as described in the repository README, then run:

```sh
python3 tools/verify.py --output build/replay-block-frequency
```

Choose a fresh output directory. The gate explicitly disables Mojo telemetry and
crash reporting and invokes the installed binaries without activation hooks.
Every one of the 63 files listed in `artifact_sha256` is included
under this directory with its exact relative path and digest. Native executables
and project proof objects are rebuilt during replay; executable hashes are
recorded in the report. Hosted GitHub Actions acceptance is a separate result
and is not asserted by this local packet.
