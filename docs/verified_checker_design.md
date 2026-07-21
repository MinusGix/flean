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

## Near-term build order

1. Raw tensor interchange: fix a trivial on-disk format (header + row-major little-endian
   float32 words); Python exporter from checkpoints; Lean `IO` reader returning
   `Array (Array UInt32)`.
2. Executable Binary32 forward-pass core on `UInt32` words, tied to Flean spec ops through
   `IntegerEquivalence` (add/mul/fma/relu exist; check exp/div coverage for softmax — the
   attention softmax is the main gap to survey).
3. First checker + soundness theorem: `checkModAdd` for the p=113 architecture; run it on the
   Nanda seed-0 checkpoint (empirically: 100% accuracy, min float32 logit margin ≈ 9.605).
4. Analysis emitters: learned-frequency detection, margin table, per-layer interval/affine
   range certificates feeding the gauge-invariant representation theorems.
