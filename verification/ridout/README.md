# Ridout replay and golden-ratio specialization

This isolated package uses Lean 4.35.0-rc3 and Subspace-Theorems commit
2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d. The root application keeps its existing
Lean 4.34.0-rc2 toolchain. The GoldenNormality modules are compiled directly from
the same checkout through srcDir = "../.."; no contract or carry theorem is copied.

## The proof

For an irrational algebraic real ξ in (0,1), Ridout's theorem is applied with
no numerator primes, the single denominator prime 2, and epsilon = 1/B.
Its height is the reduced rational height max(|num|,den). Restricting candidates
to [0,1] makes this height equal to den. The denominator of p/2^m divides 2^m,
so the external prime-product identity gives the exact factor 1/den, including
when p is even. The powered candidate condition is converted to Ridout's real
exponent inequality without weakening the exponent.

If the eventual dyadic inequality failed, the resulting reduced dyadic
candidates would approach ξ arbitrarily closely. An irrational real has positive
distance from every member of a finite set of rationals, giving a contradiction.
This handles repeated representations of the same rational; no injectivity of
(m,p) -> p/2^m is assumed.

The application proves algebraicity of alpha from X^2+X-1, uses the existing
irrationality theorem, and targets the exact BinaryComplement.EventualDyadicSeparation
definition. Its source then applies the existing carry transfer to state:

* For c >= 0 and c^2 < 2, eventually the actual original zero count exceeds
  c*sqrt(N).
* For c >= 0 and pi*c^2 < 8, arbitrarily late prefixes exceed c*sqrt(N).

These are ineffective square-root-scale bounds. They do not give frequency 1/2,
positive lower density, block normality, or cancellation of the actual binary orbit.

## Replay and acceptance

Run from this directory:

    python3 replay.py

The replay verifies every locked dependency revision and tracked-source
cleanliness, obtains the required Mathlib cache roots, builds the selected
proof closure, and records source hashes and a compiled axiom audit under build/.
The audit fixes the full Ridout type and the exact dyadic and zero-count types,
and permits only propext, Classical.choice, and Quot.sound. A rational zero control
shows why algebraicity alone cannot imply the all-numerator separation statement.

Only a successful replay at the exact source revision is proof acceptance.
A missing toolchain, failed build, absent audit marker, changed dependency or
source file is a failure. This package does not invoke all upstream default
libraries: unrelated paper targets at this pin include an absent NairKumarRout2025
directory.

This is a proof-only acceptance lane. It is separate from the root project's full
native Mojo/Python acceptance. A successful isolated replay does not migrate the
root toolchain or make this dependency available to the root default build.

## Provenance

The application is stacked on PR #32 at
a680e02f70e68f50194ee981e7d8d7701e3833a5. The imported theorem is Ridout's classical
theorem, formalized in rwst/Subspace-Theorems; this adapter claims no new classical
normality theorem. External source remains in its pinned Apache-2.0 dependency.
