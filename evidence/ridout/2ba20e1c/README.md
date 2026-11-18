# Accepted local Ridout replay

The proof-only replay passed at exact source revision
`2ba20e1ceee5b3a270e501983faccf4edfe92384` on 2026-11-15.
This directory is an evidence-only addition after that source revision.

The checked environment was Lean 4.35.0-rc3, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, with all thirteen dependency
revisions fixed by the isolated manifest. The official Linux release archive
was checked against SHA-256
`1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997`.

The targeted Lake build completed successfully (4152 jobs), and the typed
contract witnesses and boundary controls elaborated with `autoImplicit=false`
and `warningAsError=true`. The ten audited theorems all had exactly the allowed
transitive axiom set: `propext`, `Classical.choice`, and `Quot.sound`.

## Evidence

- `evidence.json` records the source revision, dependency revisions, 117 imported
  source modules, 122 source/configuration Git-blob bindings, commands, and hashes.
- `axioms.log` records the actual compiled theorem types and transitive axioms.
- `replay.log` is the successful replay's complete output.

Reproduce from `verification/ridout` at the source revision above, with its
pinned Lean binary on `PATH`:

```bash
python3 replay.py
```

The replay rejects changed source, configuration, dependency revisions, or
unexpected axioms. It uses the matching Mathlib cache and compiles the external
and application source as needed. These are local proof-only results; the
GitHub Actions run has its own status and evidence. The main project's Lean
4.34.0-rc2/native acceptance is a separate gate.
