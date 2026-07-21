# Session prompt: first verified checker (modadd network)

Read `docs/verified_checker_design.md` and the tail of `.claude/notes/modadd-transformer.md`
(2026-07-21 entries), then build the first verified network-analysis program.

**Context.** Bulk weights stay OUT of Lean (checkpoints = data, not proof-data). Pattern:
Lean spec on `FiniteFp` semantics → executable checker (`Bool`/report) → parametric soundness
theorem `check W = true → P W` → `lake exe` on raw on-disk tensors. Target artifact: Nanda's
grokked `(a+b) mod 113` transformer, `references/large_files/full_run_data.pth` (456MB, final
epoch; ground truth via `references/eval_modadd.py`: 100% accuracy, min fp32 logit margin
9.605, freqs {14,35,41,42,52}). Architecture: 1 layer, d_model 128, 4 heads × 32, ReLU MLP 512,
no LayerNorm, vocab 114, ctx `[a,b,'=']`. The retired literal path is commit `f5e1062` if
reference is needed.

**This session, in order:**
1. Raw interchange: trivial binary format (header + row-major little-endian float32 words),
   Python exporter, Lean `IO` reader → `Array (Array UInt32)`.
2. Survey executable Binary32 op coverage (`IntegerEquivalence/*`, `ExpComputable`,
   `Softmax`, `FpMatVec`): can we RUN add/mul/fma/div/exp/relu fast in compiled Lean, with
   soundness lemmas tying them to spec `FiniteFp` ops? Softmax `exp`/`div` = expected gap.
3. First checker + soundness theorem, sized to what (2) supports — even just "logit-layer
   argmax matches labels given precomputed activations" is fine as the walking skeleton;
   the full forward pass can come later.
4. Run it on the checkpoint; record the concrete result in the notes.

**Discipline:** concrete number or real-net statement per step; the soundness theorem must
quantify over all inputs (no per-checkpoint kernel decide). Keep proof code and executable
code cleanly separated.
