# Flean Issue Roadmap

Last updated: 2026-02-20

## Current status notes

- #3 is closed.
- #28 is closed.
- #15 is not done yet; cleanup/rescoping needed.
- #23 (ENNRat) is partially built but still needs substantial work.
- #35 is now started locally: initial `nextUp` / `nextDown` API landed, including zero-behavior lemmas.
- #36 is now in-progress locally: added normal-range successor/predecessor rewrite lemmas, a finite-gap `≤ ulp` theorem, `nextUp`/`nextDown` one-sided ULP corollaries, and bundled interior-hypothesis APIs for cleaner theorem use.

## Milestone 0: Backlog hygiene

- [x] #3 Division by power of 2 is equivalent to exponent shift.
- [x] #28 branchless 6-op 2Sum.
- [ ] #15 Full FP Total Order: clean up semantics and scope (current implementation exists but needs polish/decision).
- [ ] #23 ENNRat: rescope to concrete remaining gaps and finish integration quality.
- [ ] #4 Full interval module: extract and stabilize reusable interval API from existing interval reasoning.

### Acceptance criteria for #15 (Full FP Total Order cleanup)

- [ ] Document exact intended semantics against IEEE `totalOrder` (NaN ordering, signed zero ordering, infinities).
- [ ] Decide and document whether default `≤` stays current custom order or switches to IEEE-style total order.
- [ ] If default stays custom: add explicit IEEE-named comparator/API and bridging lemmas.
- [ ] Add theorem set for reflexive, antisymmetric, transitive, total properties on `Fp`.
- [ ] Add focused tests/examples for edge cases: `-0/+0`, `±∞`, quiet/signaling NaN placeholders/payload-agnostic behavior.
- [ ] Update README/docs to avoid ambiguity about which order is used where.

### Acceptance criteria for #23 (ENNRat / ERat for computable `toVal`)

- [ ] State project intent clearly: primary goal is a computable codomain for `toVal` and proof ergonomics over numeric domains.
- [ ] Define/confirm canonical embeddings `FiniteFp -> ENNRat` and `Fp -> ERat` (or equivalent shape) with simple API.
- [ ] Prove round-trip/consistency lemmas needed for reasoning workflows (coercions, sign handling, infinities).
- [ ] Ensure arithmetic/order lemmas required by existing operation proofs are available without excessive boilerplate.
- [ ] Add a small set of end-to-end examples showing proofs done via ENNRat/ERat instead of ad hoc special-casing.
- [ ] Add guidance on when to use `R`-generic proofs vs ENNRat/ERat-specific proofs.
- [ ] Mark as deferrable: defer full polish until core operation/API milestones are complete.

## Milestone 1: Neighbor and ULP API

- [ ] #35 nextUp / nextDown: public API with complete special-case behavior.
- [ ] #36 Predecessor/successor distance properties: prove link to ULP in normal range and document edge cases.

## Milestone 2: Operation API completeness

- [ ] #1 fp{Op}Correct: top-level wrappers including special-case behavior.
- [ ] #2 Monotonicity of operations: add operation-level monotonicity theorems.
- [ ] #11 roundToIntegral.
- [ ] #10 Remainder.
- [ ] #12 minNum / maxNum / minNumMag / maxNumMag / minimum / maximum.

## Milestone 3: Format and exponent utilities

- [ ] #19 formatOf.
- [ ] #34 Format Conversion (convertFormat).
- [ ] #13 scaledB.
- [ ] #14 logB.

## Milestone 4: Error-analysis layer

- [ ] #33 Error propagation framework (`δ`, `γ_n` style composition).
- [ ] #8 Ability to convert math definitions over numbers into versions over floats for analysis.

## Milestone 5: EFT to numerics stack

- [ ] #16 augmentedMultiplication.
- [ ] #32 Veltkamp Splitting.
- [ ] #37 Double double arithmetic.
- [ ] #30 Kahan Summation.
- [ ] #31 Compensated dot product.

## Milestone 6: Validation and external semantics

- [ ] #7 Validate against soft float implementations.
- [ ] #9 Validate against GPU floating point.

## Milestone 7: Research and long-horizon

- [ ] #17 RSqrt.
- [ ] #18 Transcendentals.
- [ ] #20 Decimal Parsing.
- [ ] #26 Orthogonalization stability.

## Important missing proof areas (proposed new issues)

- [ ] IEEE exception flags semantics: invalid, divide-by-zero, overflow, underflow, inexact.
- [ ] NaN payload/signaling semantics and propagation.
- [ ] Tight ULP-level forward error theorems for add/mul/div/sqrt/fma.
- [ ] Tininess and underflow policy proofs (before/after rounding behavior).
- [ ] Signed-zero behavior contracts for all top-level operations.

## Next iteration targets

- [ ] Break Milestone 1 into concrete PR-sized tasks.
- [ ] Review and refine acceptance criteria for #15 and #23 after first cleanup PRs.
- [ ] Pick 1-2 high-leverage issues for the next sprint.
