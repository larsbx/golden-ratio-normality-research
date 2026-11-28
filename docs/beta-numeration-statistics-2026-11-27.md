# Beta-numeration statistics and integer-base normality: separate research targets (2026-11-27)

Research design only. No new proof compilation, statistical experiment, or change to NormalInBase, proof status or dependency pins.

## Scope and ownership

The current project concerns ordinary integer-base digits of alpha=phi-1, not digits in base phi. Indeed alpha has greedy phi-expansion 1000... (and unrestricted alternative (01)^infinity). It is not a sample for phi-normality, and statistics of phi-expansions do not prove ordinary binary normality of phi. The binary digit automaton reads a Fibonacci integer representation of 2^n and returns an integer-base digit; it does not read an arbitrary fractional beta-expansion.

See [PSC research route and literature stop/go](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/366430a5d3b1adb29bbe092166a9a70f362ba408/docs/beta-numeration-research-route-2026-11-27.md) for golden-base uniqueness (only constant streams are unique on the full interval), countable-versus-continuum multiplicity on 0<x<1, metallic bases and substitution-generated transcendence candidates; [shared quadratic carry contract](https://github.com/larsbx/finite-math-kernels/blob/b4d1c4f74b389d426432fb9f7447c2bdda69e0c6/docs/beta-numeration-carry-contract-2026-11-27.md) for proposed exact infinite equality semantics. These notes are not new verified implementations. Inspected companion revisions: PSC `366430a5d3b1adb29bbe092166a9a70f362ba408`; finite-math-kernels `b4d1c4f74b389d426432fb9f7447c2bdda69e0c6`.

## Reusable checked source

At inspected revision 757dabaa1a5e23736079220853d0e56c2ddb4634:
- [Blocks.lean](https://github.com/larsbx/golden-ratio-normality-research/blob/757dabaa1a5e23736079220853d0e56c2ddb4634/GoldenNormality/Blocks.lean): count_eq_enumerated and count_append_boundary, generic over a decidable alphabet, retain overlapping occurrences and exactly the crossing correction at a chunk join. Reuse finite-word counting with the correct starting-position denominator N=L+1-k for a length-L prefix with L>=k.
- [Automaton.lean](https://github.com/larsbx/golden-ratio-normality-research/blob/757dabaa1a5e23736079220853d0e56c2ddb4634/GoldenNormality/Automaton.lean): error_step, invariant_step, classify_correct, power_input_digit show the proof pattern of binding symbolic transitions to actual numerical semantics; not a beta-stream equality proof.
- [README](https://github.com/larsbx/golden-ratio-normality-research/blob/757dabaa1a5e23736079220853d0e56c2ddb4634/README.md): square checkpoints and binary power-orbit criteria preserve all eventual block-frequency quantifiers; these remain the ordinary normality obligations.

## Statistical calibration and future design

For the greedy phi-shift, exclude 11 and eventually alternating boundary tails. For Lebesgue-almost-every starting value in [0,1), the invariant Parry measure has one-frequency 1/(phi^2+1); the two-state transition matrix in symbol order 0,1 has transitions (1/phi,1/phi^2) and (1,0), giving that stationary frequency. This is an exact algebraic calibration, not a uniform binary-word frequency.

For the Bernoulli convolution formed by fair independent digits over {0,1} on the full representable interval, normalized digits have a different almost-sure one-frequency 5/18, as discussed by [Kempton, digit frequencies in beta-expansions](https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/7719/DigitsIndig10.pdf;sequence=1). Treat this as imported literature; verify the exact normalization convention before importing the theorem into Lean. A finite leading integer part does not change an asymptotic frequency. Do not interchange these two measures or assume finite samples prove either limit.

For a specified substitution source or a finite-state random digit process, define the input measure, normalization and output language; prove that the labeled graph actually presents the measure-preserving or pushforward relation being analyzed, including boundary conventions. Only then compute exact block frequencies or effective error bounds. A graph with arbitrary edge probabilities is not the output measure of normalization. General Pisot normalization is prior art (see [Frougny](https://fpsac-archive.github.io/FPSAC93/ARTICLES/Frougny.pdf)); the target is a source-bound correspondence or a new quantitative result, not a novelty claim about finite-state normalization.

## Acceptance plan and negative controls

Reuse the generic block-count theorem rather than duplicate it. Keep canonical Mojo and independent Python oracle roles, upstream shared arithmetic and automata pins, exact digit source identity and Lean certificate semantics. Controls: no-11 tails 1000... and (01)^infinity evaluate equally but are different words; the forbidden 11 block has zero greedy phi-frequency, not 1/4; a finite digit sample establishes no limit; integer-base power inputs cannot be replaced by arbitrary Fibonacci words; distinct input measures cannot be merged. Future tests must run the repository's tools/verify.py and preserve exact revision, compiled types and axiom audit. No local gates executed for this documentation-only note. No current normality claim is promoted, and all beta-specific proofs and experiments remain future work.
