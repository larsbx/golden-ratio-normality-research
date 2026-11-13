# Accepted normality-criteria and checkpoint evidence

**Result: accepted.** This packet records a completed local acceptance run.

- Source commit: [`20454800b7c5320ce96a3703aa53749a914289a3`](https://github.com/larsbx/golden-ratio-normality-research/commit/20454800b7c5320ce96a3703aa53749a914289a3).
- Source tree: `dace013aae916af44100b5f9324d44416b4fff3f`.
- The source checkout was clean at the start. Project source hashes and all dependency revisions were checked again before acceptance.
- Started (UTC): 2026-11-13T09:19:04.529056+00:00.
- Finished (UTC): 2026-11-13T09:23:03.052054+00:00.
- Lean: Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release).
- Mojo: Mojo 1.1.0.dev2026090805 (34562fa1).
- Full result: [report.json](report.json).
- Compiled dependency audit: [declaration-axioms.json](declaration-axioms.json).
- Native records: [native/receipts.json](native/receipts.json).
- Generated finite theorems: [native/Receipts.lean](native/Receipts.lean).
- Independently generated exact receipt types: [ReceiptContracts.lean](ReceiptContracts.lean).
- Compiled semantic counterexamples: [BridgeCounterexamples.lean](BridgeCounterexamples.lean) and [CriteriaCounterexamples.lean](CriteriaCounterexamples.lean).
- Public theorem types and complete audit output: [lean-Audit.json](lean-Audit.json).

This evidence-only child preserves the accepted source files. The report names
the source revision that existed during the run, separately from the later
commit that records its evidence. Both earlier evidence packets remain intact.

## Observed checks

All **25 Python test methods** passed. Actual Mojo producers agreed with the
independent oracle on all **10 prefix/count cases** and all **128 Fibonacci
inputs**. All **eight invalid native requests** were rejected with their required
diagnostics. The native run used the pinned finite-math-kernels revision
`3573dc4318f4d5ccd6a103b470dc82bed1f798a8`.

The generated receipt module contains exactly **3,237 required theorem
declarations**: 783 prefix certificates, 773 digit equalities, 10 whole-word
bindings, 318 computational counts, 318 actual-digit counts, 318 occurrence
equalities, 318 exact discrepancy equalities, 128 triples of Fibonacci-value,
classification, and arithmetic-output facts, 7 power-input digit facts, and
**8 universally quantified finite-interval bounds**.

A separate module verifies **644 exact receipt types**: 318 occurrence
equalities, 318 discrepancy equalities, and 8 interval statements. The expected
counts are recomputed directly from the fixed contract and independent
sqrt/slice oracle. The interval wrappers retain the quantifier over every N
between the two complete-start counts, including both endpoint inequalities.

All **16 Lean rejection controls** passed. The 11 inherited controls cover false
root and digit/count claims, a weakened public theorem, direct and inherited
extra assumptions, unequal encoding lengths, an out-of-alphabet symbol,
empty-pattern transfer, an extra start in a short prefix, and a weakened
discrepancy receipt. The five new controls reject an out-of-range decoder
alphabet claim, an invalid width-zero round trip, omission of the checkpoint
gap, a constant checkpoint sequence claimed to be strictly increasing, and
substitution of an endpoint-only fact for a quantified interval theorem.
Each of the ten isolated bridge/criteria controls emitted exactly its one
intended error.

The compiled audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
It inspected all **4,524 declarations** across **16 modules**,
including helper declarations created by Lean, and checked all **22 explicit
public contract wrappers**. There are 4,252 theorem declarations among
those modules; these totals are not counts of independent new mathematical results.

| Compiled module | Declarations | Theorem declarations |
| --- | ---: | ---: |
| `BridgeCounterexamples` | 6 | 6 |
| `CriteriaCounterexamples` | 17 | 16 |
| `GoldenNormality` | 0 | 0 |
| `GoldenNormality.Automaton` | 237 | 157 |
| `GoldenNormality.BlockNumerals` | 39 | 28 |
| `GoldenNormality.Blocks` | 61 | 44 |
| `GoldenNormality.Certificates` | 20 | 14 |
| `GoldenNormality.CheckpointBounds` | 15 | 15 |
| `GoldenNormality.Contracts` | 22 | 22 |
| `GoldenNormality.FrequencyBridge` | 16 | 16 |
| `GoldenNormality.Normality` | 5 | 3 |
| `GoldenNormality.NormalityCriteria` | 11 | 9 |
| `GoldenNormality.Prefix` | 35 | 26 |
| `GoldenNormality.WordEncoding` | 21 | 15 |
| `ReceiptContracts` | 644 | 644 |
| `Receipts` | 3375 | 3237 |

## Mathematical scope

The fixed-width decoder covers every `j < b^k` with exactly one alphabet word
of width k, retaining leading zeros and the permitted width-zero case.
`NormalInBase b` is proved equivalent to the word formulation and to a threshold
shared by all block values at each fixed positive k and T. The threshold still
depends on k and T; the equivalences do not establish the open eventual bound.

For `D(N) = Nat.dist (b^k * occurrences b k j N) N`, the universal checkpoint
theorem proves

```text
L <= N <= R  =>  D(N) <= max(D(L), D(R)) + (R - L).
```

Consequently, an endpoint budget `(max(D(L), D(R)) + (R-L))*T <= L` supplies
`D(N)*T <= N` for every N in that closed interval. The source-bound version
consumes two exact `DigitsAt b 0` bindings and exact counts of the same
nonempty alphabet pattern. Both complete-window formulas remain explicit.

The new finite fixture uses binary prefixes of 224 and 256 digits, block
width three, and T=2. Thus L=222 and R=254. For every one of the eight block
values, the endpoint budget is at most 222 (the largest is 188). The eight
compiled interval theorems prove

```lean
forall N, 222 <= N -> N <= 254 ->
  Nat.dist (2^3 * occurrences 2 3 j N) N * 2 <= N
```

for each j from zero through seven. These are 33 possible start counts per
pattern, covered through interpolation; no patterns are filtered.

The conditional `normalInBase_of_checkpoint_bounds` theorem retains the
unresolved infinite hypothesis: for every valid k,j and positive T, a strictly
increasing sequence on all natural indices must satisfy the endpoint budget
at every sufficiently late interval. Strict increase guarantees coverage of
every sufficiently large N. No such eventual budget for the golden ratio is
provided by this packet.

The compiled counterexamples show why both a gap allowance and the coverage
hypothesis matter. The actual binary digits `1001` give D(2)=0, D(3)=1, D(4)=0
for the one-symbol pattern `[1]`. The constant sequence q(i)=0 satisfies the
budget but fails strict increase. These counterexamples prevent the acceptance
gate from silently dropping the gap or strict-increase condition.

The [derivation](../../docs/normality-criteria.md) gives the exact quantifiers,
all eight endpoint budgets, and literature scope. This packet supplies no
unconditional normality theorem, eventual golden-ratio discrepancy estimate,
or universal refinement proof for native execution or either compiler.

## Replay and artifact integrity

Install the pinned dependencies as described in the repository README, then run:

```sh
python3 tools/verify.py --output build/replay-normality-criteria
```

Choose a fresh output directory. The gate explicitly disables Mojo telemetry
and crash reporting and invokes installed binaries without activation hooks.
Every one of the **79 files** listed in `artifact_sha256` is
included under this directory with its exact relative path and digest, together
with the unchanged report. Native executables and project proof objects are
rebuilt during replay; executable hashes are recorded in the report. Hosted
GitHub Actions acceptance is a separate result and is not asserted by this
local packet.
