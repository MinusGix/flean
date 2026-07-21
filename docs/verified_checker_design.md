# Verified network-analysis programs: data, not proof-data

Decision (2026-07-21, after the `ModAddNanda` literal-ingestion experiment): **bulk network
weights stay out of Lean entirely.** No tensor literals, no kernel `decide` over checkpoint
words. The literal artifact was committed once for the record and then removed; it remains
retrievable from git history.

## The pattern

Treat a checkpoint as *data* consumed by a *proven-correct program*, not as proof-data consumed
by the kernel:

1. **Spec in Lean.** A mathematical definition of the property, stated against Flean's
   `FiniteFp`/`Fp` semantics — e.g. `IsModAddNetwork W p := ∀ a b, argmax (forward W [a, b, eq])
   = (a + b) mod p`, with `forward` the Binary32-exact forward-pass specification.
2. **Checker in Lean.** An executable function `check : Tensors → Bool` (plus report-producing
   variants), written for compiled execution — bit-level `UInt32`/`BitVec` float ops, arrays,
   no kernel-friendliness constraints.
3. **Correctness theorem.** `check W = true → IsModAddNetwork W p`, proved once, over *all*
   inputs `W`. This is where the intellectual content lives; the `IntegerEquivalence` layer
   (spec `FiniteFp` ops ↔ bit-level integer ops) is the substrate that makes the checker both
   fast and provably faithful to IEEE semantics.
4. **Execution outside the kernel.** `lake exe` the checker on the on-disk artifact (a raw
   little-endian word dump exported from the checkpoint). The claim "this file's network is
   modadd" is then trusted at the level of the Lean compiler + the file-reading boundary —
   explicitly *not* a kernel theorem about the particular bytes, and we say so.

Analysis programs, same pattern, weaker outputs: frequency-subspace extraction, margin tables,
per-layer range certificates — each an executable with a proved soundness lemma ("if the program
emits certificate `c`, then property `P c` holds of the input network").

## Why this beats the two rejected alternatives

- vs. **literal ingestion** (tried): 226,816 words cost ~2.5MB source and ~15 min kernel time,
  and that was the *easy* static layer; the extensional forward pass would be orders worse. Does
  not scale past toy networks, and entangles artifact bytes with library code.
- vs. **`native_decide`**: same trusted base (compiler), but the checker pattern quantifies over
  all inputs once, produces reusable executables with legible specs, keeps proofs and data
  cleanly separated, and never tempts us to mix quarantined axioms into the mathematical core.

The parametric mathematics (margins, cyclic-representation/gauge-invariant certificates,
perturbation bounds — `ModAddClock*.lean`) is unchanged and stays kernel-pure: theorems about
*any* network satisfying an interface. Checkers are how a specific on-disk network is shown to
satisfy the interface.

## Build order and status

1. **DONE (2026-07-21).** Raw tensor interchange: FLEANTEN v1 (8-byte magic, version, per-
   tensor name/rows/cols, row-major little-endian float32 words). Exporters
   `references/export_raw_tensors.py` (11 weight tensors, 226,816 params) and
   `references/export_activations.py` (final logits + pre-unembed residual for all 12,769
   pairs). Pure parser + IO wrapper in `Flean/Checker/RawTensor.lean`; exe target
   `lake exe modadd_checker` (`Checker/Main.lean`).
2. **Surveyed (2026-07-21).** Executable-op coverage: all scalar spec ops (`fpAddFinite`,
   `fpMulFinite`, `fpFMAFinite`, `fpDivFinite`) are computable under `RModeExec` (RNE via
   `UseRoundingPolicy RoundNearestEvenPolicy`); decode is `Fp.ofBits` (computable, with
   round-trip theorems); `fpRelu`/`bitRelu` certified; `fpExp` computable via `OpRefExec`
   interval kernels — so softmax is assemblable from `fpExp` + `fpAdd` + `fpDivFinite`.
   No executable matvec/softmax/MLP exists (the library's dot-product/MLP layer is
   certificate structures, not folds) — checkers write their own folds. No native floats
   anywhere: compiled execution is exact ℚ/ℤ bignum, correct but ~µs/op.
3. **DONE, walking skeleton (2026-07-21).** First checker + soundness:
   `Flean/Checker/ModAddReadout.lean`. `specLogit` = sequential spec-Binary32 dot product
   (RNE mul/add) of a residual row with a `W_U` column; `ReadoutCorrect resid wU` = for every
   pair the true-answer logit is finite and strictly beats all 113 others in exact rational
   comparison; `checkReadout` recomputes all 12,769 × 114 logits and checks this;
   `checkReadout_sound : checkReadout resid wU = true → ReadoutCorrect resid wU` is
   parametric over all word arrays. `Flean/Checker/ModAddReadoutAccuracy.lean` bridges into
   the kernel-pure framework: `ReadoutCorrect → FailureSet (realizedLogit …) = ∅` and
   `accuracy … = 1` in the `ModAddClock` sense. Trust honestly stated: the residual stream is
   torch-exported data; the unembed layer's arithmetic is re-executed in the Lean spec.
   Run on the seed-0 checkpoint (2026-07-21): `checkReadout = true`, so `ReadoutCorrect`
   holds — 12769/12769 pairs, and the exact-rational min margin is 9.605161… (truncated),
   matching the float32 torch reference 9.6052. Report pass 861 s, verified pass ≈ 854 s
   (~67 ms/row each; exact bignum arithmetic, single-threaded).
4. Extend the recomputation upstream (MLP + ReLU next, then attention/softmax) to shrink the
   trusted-activation boundary; analysis emitters: learned-frequency detection, margin table,
   per-layer interval/affine range certificates feeding the gauge-invariant representation
   theorems.
