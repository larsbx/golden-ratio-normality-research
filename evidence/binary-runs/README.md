# Accepted binary run and recurrence evidence

The complete local gate passed on clean published source
`f3817b6053d76d5e9d948a26ef91704182171250`, tree `d0e70ec44caa03902cf8a3a93e6d7904bfdcec23`.
This packet preserves the original report and every artifact it hashes.
The evidence-only child commit preserves all 62 accepted source inputs.

## Result and scope

Every constant binary run starting at position n has length at most n+1.
Every actual window [n,2n+2) contains both symbols. For each d<2 and every m,
the first 2^(m+1)-2 digits contain at least m copies of d; every later prefix
retains that bound. The window endpoint is exclusive, and all prefix positions
are counted. These logarithmic recurrence bounds do not establish positive
density, limiting frequency one half, or normality.

The increment adds 16 public mathematical theorems in two modules, 14 explicit
public theorem-type wrappers, 41 explicit positive control statements, and
10 isolated rejection controls. Declaration totals below also include generated
helpers and finite receipt/type statements; they are not discovery counts.

## Observed complete acceptance

| Check | Result |
| --- | --- |
| Python suite | 56 tests passed |
| Native conformance | 10 prefix/count cases, 128 ordinary automaton inputs, 6 power traces with 144 input records through exponent 127 |
| Invalid native requests | 17 rejected |
| Finite receipt proofs | 3,871 passed |
| Independent receipt type checks | 1,278 passed |
| Public theorem-type contracts | 58 passed, including 14 new |
| Lean semantic/type/assumption rejection controls | 51 passed, including 10 new |
| Fresh compiled audit | 28 modules, 6,306 declarations, 5,848 theorem declarations |
| Transitive assumption allowlist | `propext`, `Classical.choice`, `Quot.sound` |

Report SHA-256: `e1fb5820e2da907a8c594e3af22620b245076c2c20213f07d8500db05554608d`.

All **182 artifact hashes** in `report.json` are retained. The report
records the source inventory, exact dependency revisions, compiler identities,
commands, outputs, and compiled declaration assumptions. Native producers,
fixture sets, bounds, and dependency pins are inherited unchanged from #6.

`source-audit.json` is a separate independent read-only source review. It
reconciles all 62 source bytes with their Git blobs and reviews the mathematics,
source bindings, public contracts, controls, and documentation. It reruns no
compilers or tests and does not substitute for the acceptance report.
Its SHA-256 is `6eb3d51bc1a21dd9b77f95f9567aff3a6cb637c6486195a8d771f06a5fa4a359`.

## Replay

Check out the source commit above with its submodule and pinned dependencies,
then run:

```sh
python3 tools/verify.py --output build/replay-binary-runs
```

The root README describes pinned Lean, mathlib, and Mojo installation and the
optional `LEAN_BIN`, `MOJO_BIN`, and `GNR_MATHLIB_PACKAGES` selectors. The gate
requires a clean checkout, fresh proof objects, exact source bytes, and a new
output directory. A missing tool or failed check cannot be counted as a pass.

This packet establishes local acceptance at its stated source revision.
GitHub Actions supplies separate exact-head hosted evidence. No universal
native/compiler refinement or independent human approval is claimed.
