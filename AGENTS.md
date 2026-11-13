# Research implementation policy

Read README.llm.txt before changing the research contracts.

## Mathematical authority

- Lean proofs determine deductive acceptance at their exact stated hypotheses.
- Do not add `sorry`, new axioms, or `native_decide` to accepted proofs.
- Preserve the distinction between a universal theorem, a checked finite object,
  a finite differential test, an imported literature theorem, and an open claim.
- Digit generation and any finite prefix test do not establish normality.
- Keep the base, block length, starting-position convention, arithmetic domain,
  source identity, and resource bounds in each executable contract.

## Implementations and dependencies

- Mojo is the canonical executable research language under kernel/.
- Python under oracles/ is an independently written oracle and certificate
  translation layer. It does not replace the canonical native producer.
- Reuse the pinned finite-math-kernels submodule for exact arithmetic. Do not
  edit its files or add a competing arbitrary-precision arithmetic package.
- Shared general-purpose improvements belong upstream; this repository owns
  the golden-ratio application and its proof obligations.
- Never treat overflow, malformed input, an exhausted budget, or a missing
  toolchain as a successful mathematical result.

## Evidence

For theorem-facing work include the hypotheses, inspectable derivation, replay
command, observed evidence, negative controls, and remaining obligations.
Perform a proportional primary-literature check before pursuing a new proposed
universal invariant. Retain counterexamples to stronger variants.

Use exact revision and content identities. Audit the actual compiled theorem
types and transitive axioms; a source-text scan is an additional check only.
Independent human review is separate from mechanical acceptance and does not
block authorized research progression.
