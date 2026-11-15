# Ridout replay and golden-ratio specialization

This isolated package uses Lean 4.35.0-rc3 and the exact Subspace-Theorems commit
2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d. The root application remains on its
existing toolchain. Its GoldenNormality modules are compiled directly from the
same checkout through srcDir = "../.."; no contract or carry theorem is copied.

## Scope

The initial replay compiles the actual Rat.finite_setOf_ridout and the existing
BinaryGapTransfer import closure, checks an independently stated full Ridout type,
and rejects transitive axioms outside propext, Classical.choice, and Quot.sound.
The dyadic specialization is the remaining implementation task in this branch.
Until that task compiles and is audited, EventualDyadicSeparation remains an
explicit hypothesis and neither stronger zero-count consequence is unconditional
in this package.

Run from this directory:

    python3 replay.py

The replay verifies every locked dependency revision and tracked-source
cleanliness, obtains only the required Mathlib cache roots, builds the selected
proof closure, and records its source hashes and compiled audit under build/.
It intentionally does not invoke all upstream default libraries: unrelated
paper targets at this pin include an absent NairKumarRout2025 directory.

This is a proof-only acceptance lane. It is not the root project's full native
Mojo/Python acceptance and does not establish binary normality.
