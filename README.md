# Golden ratio normality research

Mechanically checked foundations for investigating the fractional digits of
φ = (1 + √5) / 2 in integer bases.

**Normality remains open.** This repository separates universal mathematical
proofs, certified finite computations, implementation tests, published results,
and unresolved asymptotic claims. A large digit sample is never labeled a proof
of normality.

## Proved contracts

| Layer | Contract |
| --- | --- |
| Exact roots | A natural-number inequality certificate is equivalent to `q = floor(B(φ−1))`, for every positive scale `B`. |
| Digits and blocks | Adjacent prefixes determine an actual digit; a length-`k` block is `floor(b^k frac(b^n(φ−1)))`. |
| Contiguous counting | Overlaps are retained; a chunk join needs only the last and first `k−1` symbols for its boundary correction. |
| Frequency bridge | For every base `b≥2`, nonempty alphabet pattern of length `k`, and actual prefix of length `L`, the list count equals `occurrences b k j (L+1−k)`. Short prefixes give zero starts. |
| Equivalent targets | Every bounded block value has a unique word of its specified width. Normality is equivalent to eventual word-count bounds, with one threshold for all values of each fixed width and tolerance. |
| Checkpoint bounds | Two certified endpoint counts control every intermediate start count. A conditional criterion retains a strictly increasing infinite checkpoint sequence and eventual budgets for every block and tolerance. |
| Sparse checkpoints | Normality is equivalent to endpoint convergence along any strictly increasing sequence with vanishing relative gaps. Squares satisfy that geometry with an explicit threshold, giving an equivalent binary power-orbit target at square numbers of starts. |
| Binary automaton | A universal real invariant verifies the published eight-state Fibonacci-input machine and its specialization to inputs representing `2^n`. |
| Power-orbit evaluation | A total Fibonacci-word encoder makes the automaton's outputs at `2^n` a computable digit sequence. Its words and block counts equal the actual binary digit words and counts, with all normality quantifiers retained. |
| Native receipts | Pinned Mojo and upstream BigZ produce finite records; an independent Python oracle checks them, and Lean verifies their digits, occurrences, discrepancies, and finite interval bounds. |
| Open target | `NormalInBase` states all block-frequency quantifiers for the actual digits. No unconditional proof is supplied. |

The automaton is due to Barnoff, Bright, and Shallit; see
[the literature gate](docs/literature-gate.md). The repository contribution is
its explicit Lean proof and the application-specific certificate pipeline.
See [the mathematical foundation](docs/foundation.md) for derivations and limits,
the [block-frequency bridge](docs/block-frequency-bridge.md) for the exact count transfer,
the [normality criteria and checkpoints](docs/normality-criteria.md) for the next proof interface,
the [power-orbit bridge](docs/power-orbit.md) for total evaluation and source-bound native traces,
the [sparse checkpoint criterion](docs/sparse-checkpoints.md) for endpoint estimates and square checkpoints,
and [the claim ledger](claims.json) for the classification of each claim.

## Reproduce acceptance

The checked environment is Linux x86-64, Lean **4.34.0-rc2**, the exact mathlib
revision in `lake-manifest.json`, and Mojo **1.1.0.dev2026090805** in the committed
Pixi lockfile. CI uses Pixi **0.84.2**. Install Elan and that Pixi version, then run:

```sh
git clone --recurse-submodules https://github.com/larsbx/golden-ratio-normality-research.git
cd golden-ratio-normality-research
lake exe cache get
pixi install --manifest-path kernel/pixi.toml --locked
kernel/.pixi/envs/default/bin/python tools/verify.py
```

The full gate compiles fresh project proof objects, inspects compiled axiom
dependencies and explicit public theorem types, builds the Mojo executables,
checks the independent oracle, compiles the generated finite certificates,
independently checks every occurrence, discrepancy, and interval receipt's exact type,
and every new power-orbit receipt's source, digit, and count type. It verifies
negative controls and writes `build/acceptance/report.json`.
An existing nonempty output directory is rejected; choose a new one with
`--output build/another-run` when repeating a run.

For an already installed toolchain, `python3 tools/verify.py` is sufficient.
`LEAN_BIN`, `MOJO_BIN`, and `GNR_MATHLIB_PACKAGES` can select existing pinned
installations; the gate checks their versions and dependency revisions.
Missing tools or failed stages are failures, never skips.

The runner explicitly disables SDK telemetry and crash uploads before invoking
Mojo. It calls installed executables directly; CI does not activate the Conda
environment, whose activation hook in this pinned package sends a separate event.
Compiler scratch files use a temporary directory on the project volume and are
removed after native compilation.

`bash tools/check_native.sh` runs only native/oracle conformance and emits Lean
obligations. Its successful exit alone does not establish Lean acceptance.

## Conventions and limits

- Digit positions are zero-indexed after the radix point; φ and φ−1 have the
  same fractional digits.
- Blocks are consecutive, may overlap, and include leading-zero words.
  A prefix of `L` digits has `max(0,L+1−k)` complete starts for `k≥1`;
  choosing `L=N+k−1` gives exactly `N` starts.
- The first native producer supports bases 2–10, prefix lengths 0–4096, and
  block widths 1–4. These are execution bounds, not hypotheses restricting
  the universal root or block theorems.
- Fibonacci words are read most significant first, with rightmost weights
  1, 2, 3, 5, … . Adjacent ones are rejected; leading zeros are allowed.
- The power-orbit producer supports binary segments of at most 256 digits,
  with nonnegative start, end at most 4096, and block width 1–4. Its powers
  stay in upstream BigZ; every input is bound to its exact exponent.
- The compiled axiom allowlist is `propext`, `Classical.choice`, and
  `Quot.sound`. The project adds no mathematical axiom.
- Finite receipt verification does not prove universal correctness of the
  Mojo compiler or of every native BigZ operation.

## Next research obligation

Control the output block frequencies along the particular input sequence
`Z(b^n)`, with the required quantifiers over block lengths and values. In base
two, total computable evaluation and its exact block-count bridge are now proved. A
complete eventual estimate at square numbers of starts is also proved sufficient;
the prefix at checkpoint `i^2` still contains `i^2+k−1` consecutive digits for
width `k`. This endpoint frequency estimate remains open. A
frequency statement over all Fibonacci words does not imply that result.
The published automaton provides exact digit evaluation; it does not supply
the missing distribution theorem.

Contributor and agent instructions are in [AGENTS.md](AGENTS.md) and
[README.llm.txt](README.llm.txt).
