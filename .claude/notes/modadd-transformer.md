# Modular-addition transformer thread (started 2026-06-15)

**The concrete target.** Aim the reduction / abstract-interpretation apparatus at a famous, concrete
network: the 1-layer transformer trained on `(a+b) mod p` (Nanda et al., *Progress measures for
grokking*), reverse-engineered to implement a **Fourier "clock"** — embed inputs as `(cos ωₖa, sin
ωₖa)` on a frequency set, combine with trig identities into `cos ωₖ(a+b)`, read off the argmax = the
sum. This is the "idealized target right in front of us" — analyze it from *what Nanda said* and
*what we can infer* (esp. FP-level structure he didn't analyze).

Why it's the ideal capstone: it lights up the whole stack at once —
- modp/`IsImage`/CRT (`ExactIntModP.lean`) = the *answer* (residue in `ZMod p`);
- the continuous tower (Affine/Quad/Poly/`MvForm`) = the trig/Fourier *mechanism*;
- the snapping bridge (`ScaledIntSnap.lean`, the `½`-margin) = the discrete readout;
- `AffineRegion`/interval = realized internal ranges;
- the probabilistic √n law (`ProbError.lean`) = **frequency redundancy as error correction** (each
  frequency an independent estimate; margin grows ~`|K|`, FP noise only ~`√|K|`).

## The load-bearing design principle (from the user, 2026-06-15)

> ML models fail on some fraction of inputs. **Never state global correctness.** State a per-input
> **margin** and make correctness mean "margin beats the error." The failure set is `{inputs : margin
> ≤ error}`; accuracy = `1 − |failure set| / p²`.

Failure decomposes cleanly into two independent sources, to be tracked separately:
1. **Structural** — the idealized algorithm itself is weak/wrong on some `(a,b)` (small margin even in
   exact ℝ). Appears once we use a *sparse* learned frequency set (margin becomes `K`-dependent).
2. **FP / snapping** — the floating-point correction exceeds the (idealized) margin.

This is the same `½`-threshold as the discrete snapping bridge, lifted to a *set-indexed* statement.
Headline degrades gracefully: "computes mod p" → "computes mod p on certified set `S`, `|Sᶜ| ≤ …`,
`Sᶜ = structural ∪ FP`." A **certified accuracy lower bound** — novel, and honest by construction.

## Build order

1. **Idealized, all/any DC-free frequency set, exact ℝ** — DONE (see below). Clean baseline: margin
   `> 0` everywhere, empty failure set. Margin object + failure criterion in place.
2. **Sparse / learned frequencies** — margin becomes `K`-dependent; structural failure set appears;
   prove "more frequencies ⇒ bigger margin" (redundancy = robustness, the √n hook).
3. **Floating point** — `δ` = FP forward-error of the logits; plug into `correct_under_perturbation`;
   certified accuracy = `1 − |{margin ≤ 2δ}|/p²`.
4. **Real weights** (stretch) — load Nanda's actual weights; validate idealized vs realized; the
   weights-into-Lean bridge is the gating engineering step (doesn't exist yet).

## Shipped — `Flean/Operations/ModAddClock.lean` (2026-06-15, sorry-free, warning-clean)

`namespace Flean.ModAddClock`, `variable {p : ℕ}` then `[Fact p.Prime]` (split so the prime-free
lemmas — `phase`, `clockLogit`, `clockLogit_self` — sit before the instance; avoids `omit` friction).

- `phase k m := 2π·(k*m).val/p` (`k,m : ZMod p`); `clockLogit K s c := ∑ k∈K, cos (phase k (s−c))` —
  score class `c` gets when the true sum is `s`, frequency set `K`.
- `clockLogit_self : clockLogit K s s = K.card` (perfect alignment, max score).
- `cos_phase_lt_one (hk : k≠0) (hm : m≠0) : cos (phase k m) < 1` — the analytic core. Phase is
  `2π·t/p`, `0<t<p`, never a multiple of `2π`; via `Real.cos_eq_one_iff` + no integer in `(0,1)`.
- `clockLogit_lt_self` — **strict argmax**: `K` nonempty & DC-free (`0∉K`) ⇒ every wrong class scores
  strictly lower. (A *single* frequency already decodes correctly; multiple = bigger margin.)
- `CorrectAt K s := ∀ c≠s, clockLogit K s c < clockLogit K s s`; `correct_everywhere` (empty failure
  set in exact arithmetic).
- `margin K s := clockLogit K s s − (univ.erase s).sup' … (clockLogit K s)` (best-competitor gap, the
  degradable quantity); `margin_pos`.
- **`correct_under_perturbation`** — the failure criterion: perturbed logit `L` within `δ` of ideal at
  every class ∧ `2δ < margin K s` ⇒ `s` still strict argmax. Contrapositive: failure ⊆ `{margin ≤
  2δ}`. This is the FP hook (`L` = actual float logit, `δ` = its forward-error bound).

Gotchas: `ZMod p` field/`NoZeroDivisors` instance is in `Mathlib.Algebra.Field.ZMod` (import it, not
just `Data.ZMod.Basic`); `NeZero p` from `⟨hp.out.pos.ne'⟩`; `Fact (1<p)` from `⟨hp.out.one_lt⟩` for
`Nontrivial`/`exists_ne` (competitor set nonempty); `n*p=t, 0<t<p` contradiction via two `nlinarith`
+ `exact_mod_cast` + `omega`.

### Added 2026-06-15 (session 2) — decoder + accuracy + FP certification bridge

Same file, all sorry-free / warning-clean:
- `IsArgmax K s c := ∀ c', clockLogit K s c' ≤ clockLogit K s c`; **`isArgmax_iff_eq`** (under
  `hK`,`h0` the argmax ⇔ `= s`) + `existsUnique_argmax`. Headline **`clock_decodes_add`**: on inputs
  `a b`, `IsArgmax K (a+b) c ↔ c = a+b` — the clock computes `(a+b) mod p`, recovered as the readout
  argmax. (`rintro rfl` substitutes `s`→`c`; write the backward branch in `c`, not `s`.)
- `FailureSet (L : ZMod p→ZMod p→ZMod p→ℝ) : Set (ZMod p × ZMod p)` — input pairs where the true sum
  is NOT the strict argmax of the realized logits `L a b ·` (general, covers FP); `accuracy L :=
  1 − (FailureSet L).ncard / p²`. Idealized: `failureSet_clock_eq_empty` + `accuracy_clock_eq_one`
  (clock = 100%, the clean baseline).
- **`failureSet_subset_smallMargin`** (THE certified-accuracy bridge): if every realized logit is
  within `δ` of the ideal, `FailureSet L ⊆ {ab | margin K (a+b) ≤ 2δ}`. Needs neither `hK` nor `h0`
  (pure perturbation arg — holds for ANY K). + `accuracy_eq_one_of_margin_gt` (margin `> 2δ`
  everywhere ⇒ `accuracy = 1`). The honest `1 − ε` version = bound the small-margin set.

### Added 2026-06-16 (session 3) — single-frequency fragility (direction #1, DONE in full)

Same file, sorry-free / warning-clean. The quantitative case for *why redundancy is forced*:
- `clockLogit_singleton` (one-term logit); `cos_two_pi_val_le`/`cos_phase_le` (every wrong-class phase
  cosine ≤ `cos(2π/p)` — cosine folds `t ↔ p−t`, then antitone on `[0,π]` via
  `Real.cos_le_cos_of_nonneg_of_le_pi` + `Real.cos_two_pi_sub`).
- `clockLogit_singleton_competitor`: the adjacent class `s − k⁻¹` is the strongest competitor, scoring
  exactly `cos(2π/p)`.
- **`margin_singleton`** (the headline): for ANY nonzero `k` and ANY `s`, `margin {k} s =
  1 − cos(2π/p)` — constant, independent of frequency and input.
- **`margin_singleton_le`**: `margin {k} s ≤ 2π²/p²` (via `Real.one_sub_sq_div_two_le_cos`) — the
  margin vanishes like `1/p²`.
- **`singleton_accuracy_eq_one_of_lt`**: a one-frequency clock is exactly correct iff the per-logit FP
  error `δ < (1−cos(2π/p))/2 ≈ π²/p²`. The crisp robustness threshold: tolerance shrinks like `1/p²`,
  so a single frequency cannot survive a fixed rounding error at large `p` ⇒ multiple frequencies
  (a larger margin) are *required* for robustness. This is the Fourier-redundancy imperative, proved.

Gotchas: `Real.one_sub_sq_div_two_le_cos` lives in `…Trigonometric.Bounds` (separate import);
`le_or_lt`→`le_or_gt` (deprecated); avoid `gcongr` on `a/p ≤ b/p` (left a junk goal) — factor
`2π·a/p = (2π/p)·a` then `le_mul_of_one_le_right`.

### Added 2026-07-10 — linear redundancy + floating-point tensor realization

Two files, sorry-free and warning-clean relative to their own declarations:

- `ModAddClock.lean` now proves the previously deferred multi-frequency lower bound directly:
  `|K|·(1-cos(2π/p)) ≤ margin K s`, and the algebraic corollary
  **`8|K|/p² ≤ margin K s`**.  The latter uses Mathlib's
  `cos x ≤ 1-(2/π²)x²` bound and is suitable for comparison with a concrete FP error without
  numerically evaluating cosine.
- The perturbation API now has per-class (`correct_under_pointwise_perturbation`) and per-input
  (`failureSet_subset_smallMargin_inputwise`) forms.  This corrects an important modeling issue: the
  ideal clock margin is translation-invariant, so one global `δ` cannot by itself express a genuine
  fractional input accuracy.
- New `ModAddClockFp.lean` introduces `FrequencyBank p n`, a `Fin n`-indexed frequency bank suitable
  for tensors; its `2n` cosine/sine `feature`; and `feature_dot_eq_clockLogit`, proving that the
  feature/readout dot product is exactly the existing ideal phase-sum specification.
- `FpClockTables` stores actual `FiniteFp` input features and readout rows with explicit coordinate
  approximation bounds. `FpClockExecution` consumes an `FpMatVecBound` for every sum and exposes
  the computed finite logits.
- `logit_error_le` is the end-to-end bridge.  Its error is split into
  `arithmeticError` (from `FpMatVecBound`) plus `quantizationError` (stored table/input deviation).
- `failureSet_subset_certifiedBadInputs` gives the exact-margin certificate;
  `failureSet_subset_algebraicBadInputs` gives the concrete-shape `8n/p²` over-approximation.

Model boundary: `FpClockTables.input` represents the recovered Fourier feature of the sum.  The
current layer verifies storage + readout, while construction of that feature from separate `a` and
`b` embeddings (rounded trig identity / learned upstream network) remains the next mechanism layer.

### Added 2026-07-10 — canonical Binary32 Fourier tables

New `Flean/Operations/ModAddClockBinary32.lean`:

- fixes the format to `FloatFormat.Binary32` and rounding to nearest-even;
- defines each entry as the actual finite RNE result of the exact Fourier coordinate;
- proves finiteness from `|sin|,|cos| ≤ 1` and the Binary32 largest-finite bound;
- certifies every coordinate with
  `tableError = 2⁻²⁴ + 2⁻¹⁵⁰` via `round_preserves_abs_error_unified`;
- defines `tables B : FpClockTables B` for any bank;
- defines `fullBank113` (frequencies `1,…,112`) and proves its finset is `univ.erase 0`;
- defines `fullTables113`, the canonical `113 × 224` Binary32 cosine/sine table;
- proves the full-bank algebraic margin `896/12769 ≤ margin` and gives the closed-form 224-coordinate
  quantization contribution.

The values are canonical mathematical `FiniteFp` roundings, not host-evaluated bit-pattern literals:
Mathlib's real trig functions are noncomputable. Literal export is a separate interval-certificate
engineering step, not assumed by the correctness result.

### Added 2026-07-21 — end-to-end separate-input Binary32 clock

`Flean/Operations/ModAddClockBinary32EndToEnd.lean` constructs the Fourier feature from separate
`a` and `b` table rows using rounded cosine/sine addition identities, evaluates the 224-coordinate
readout with sequential Binary32 FMA, and proves `endToEndAccuracy113_eq_one`. The theorem therefore
removes the recovered-`a+b`-feature oracle from the concrete `p=113` result.

### Added 2026-07-21 — literal Binary32 certificate boundary

`Flean/Operations/ModAddClockBinary32Literal.lean` adds `FiniteWord`, whose decoded `FiniteFp`
provably re-encodes to its original `BitVec 32`, plus certified literal vectors and a direct
conversion to `FpClockTables`. `fullBank113ZeroRow` is the first complete literal row: 112 one words
and 112 zero words, certified exact. The initial proposed follow-up was bulk generation and interval
certification of the nontrivial trig rows; the architecture correction below supersedes that plan.

### Architecture correction 2026-07-21 — tables are a backend, not the mechanism

The stronger objection to finishing the literal trig table is architectural, not just its size.
`FpClockTables` fixes a canonical sine/cosine basis and validates implementations entrywise. A
learned network may realize the same cyclic representation after frequency permutation, rotation or
rescaling inside each frequency plane, and a paired change in its readout. Entrywise closeness to our
chosen gauge is therefore the wrong invariant.

The next core should be representation-first. An approximate cyclic-code interface should expose an
encoded state, separate-input combination, candidate scoring, composition/score defects, arithmetic
error, and a margin theorem. The exact Fourier clock becomes one instance; literal tables,
recurrences, and learned weights become backends. Real weights should be certified through detected
frequency subspaces, changes of basis, residual bounds, and operational defects. See
`docs/modadd_clock_representation.md`.

Keep extensional verification separate from mechanism explanation. At `p=113`, an imported concrete
network has only 12,769 input pairs, so an executable/reflected forward-pass certificate can establish
its actual accuracy directly. The gauge-invariant cyclic-representation certificate then explains
the behavior and its robustness; it is not a prerequisite for the finite correctness result. Inspect
the chosen checkpoint before freezing the new structural API.

The literal bridge remains useful as generic bit-exact artifact ingestion. Do not extend it into a
full canonical table unless a concrete reference-backend use requires that artifact.

### Added 2026-07-21 (session 2 of the day) — REAL WEIGHTS IN LEAN (#3 first half)

Checkpoint acquired and inspected (the "inspect before freezing the API" gate):

- **Artifact**: `references/large_files/full_run_data.pth` (456MB, gdown id
  `12pmgxpTHLDzSNMbMCuAMXP1lE_XiCQRy`, from `neelnanda-io/Grokking` / progress-measures-paper
  helpers). Mainline run: seed 0, p=113, d_model=128, 1 layer, 4 heads × d_head 32, d_mlp 512
  ReLU, **no LayerNorm**, vocab 114 (`0..112` + `=`), ctx `[a,b,=]`, frac_train 0.3, 500 saved
  epochs; we use the final (epoch 49900) `model` state dict. Repos cloned under `references/`.
- **Extensional numbers** (`references/eval_modadd.py`, float32 torch forward, all 12769 pairs):
  **accuracy 100%** (argmax over all 114 or over 0..112), **min margin 9.6052**, mean 17.12,
  max 21.59, 0.1% quantile 11.9. `=`-logit never beats the best wrong answer. Huge margin vs
  any plausible FP forward error — the certificate has lots of room.
- **Fourier check** (rfft of W_E over input dim): key frequencies **{14, 35, 41, 42, 52}**
  (paper's exact set), ≈93.9% of non-DC power. Weight maxima per tensor all ≤ 0.298.
- **Lean ingestion shipped** (`Flean/Operations/ModAddNanda/`):
  - `Packed.lean` — `PackedMatrix r c T`: rows as single packed ℕ (little-endian 32-bit words),
    ONE `decide` certificate per tensor = fused per-word check `checkWord T w` (finite ∧
    `m·2^((e−min_exp).toNat) ≤ 2^T`, pure ℕ arithmetic so the kernel never touches ℚ/ℝ).
    Bridges: `word_isFinite`, `value : FiniteFp`, `value_toBits` (bit-exact re-encode, via
    Literal.FiniteWord), `abs_value_le` (`|toVal| ≤ 2^(T+min_exp−prec+1)`), `abs_value_le'`
    (explicit `2^t` with `by decide` side condition — avoids private-local-instance rw friction).
  - Generated `Embed.lean`/`Attn.lean`/`Mlp.lean` (via `references/export_weights.py`): all 11
    learned tensors, 226,816 params, bit patterns as hex row-nats. `set_option maxHeartbeats 0`
    required. decide cost ≈ 3ms/word (Embed 29.5k words ≈ 85s).
  - `ModAddNanda.lean` umbrella: provenance docstring, `paramCount`, per-tensor magnitude
    bounds `wE/wPos/wU ≤ 2⁻¹`, `wK ≤ 2⁻³`, `wQ ≤ 2⁻⁴`, `wV/wO ≤ 2⁻¹`, `wIn/wOut ≤ 2⁻²`,
    `bIn ≤ 2⁻³`, `bOut ≤ 2⁻⁵`.
- W_K/Q/V exported flattened `(4·32, 128)`; mask not stored (structural tril, not learned).

**PIVOT (same day, user decision): literal artifact COMMITTED THEN REMOVED.** Commit `f5e1062`
has the full artifact (retrievable); `d0d3105` removes it. Even at 227k params the literal path
is rough (2.5MB source, ~15 min kernel decide, invalidated wholesale by any Packed.lean touch),
and it was the *easy* static layer. New architecture = **verified checkers**
(`docs/verified_checker_design.md`): bulk weights stay OUT of Lean entirely, checkpoints are
*data not proof-data*. Pattern: (1) spec in Lean against FiniteFp semantics (e.g.
`IsModAddNetwork W p`), (2) executable checker `check : Tensors → Bool` written for compiled
execution (UInt32/bit-level, `IntegerEquivalence` layer as substrate), (3) soundness theorem
`check W = true → P W` proved parametrically over ALL W, (4) `lake exe` on raw on-disk word
dump — trust boundary = Lean compiler + file read, stated honestly, NOT kernel decide.
Kernel-pure mathematics (margins, gauge-invariant representation certs) unchanged. Relevant
existing substrate spotted in Operations.lean: `ExpComputable`/`LogComputable`, `Softmax`,
`FpMatVec`, `MLP`, `IntegerEquivalence.*` (ReluBits etc.).
- Next: (a) raw tensor interchange format + Lean IO reader; (b) survey executable-op coverage
  (exp/div for softmax = main gap); (c) `checkModAdd` + soundness for the p=113 architecture,
  run on the seed-0 checkpoint; (d) analysis emitters (frequency detection, margin table,
  range certs) feeding the representation-first core (#2g).

### Added 2026-07-21 (session 3 of the day) — FIRST VERIFIED CHECKER (#3b walking skeleton)

Shipped the first spec + executable checker + parametric soundness theorem + compiled run,
per `docs/verified_checker_design.md` (status now recorded there too).

- **Interchange (FLEANTEN v1)**: magic `FLEANTEN` + version + per-tensor
  name/rows/cols + row-major LE float32 words. `references/export_raw_tensors.py` (11 weight
  tensors, 226,816 params, `modadd_weights.fleanten`, 907KB);
  `references/export_activations.py` (final logits 12769×114 + pre-unembed residual
  12769×128, float32 sanity in-script: acc 1.0, min margin 9.6052). Lean side
  `Flean/Checker/RawTensor.lean`: pure parser `ByteArray → Except String (Array RawTensor)`
  + `readRawTensorFile`; exe `lake exe modadd_checker` (`Checker/Main.lean`, new lakefile
  `lean_exe` — first executable target in the repo).
- **Op-coverage survey** (Explore agent, detailed table in its report / design doc): scalar
  spec ops `fpAddFinite`/`fpMulFinite`/`fpFMAFinite`/`fpDivFinite` all COMPUTABLE under
  `[RModeExec]` (RNE = `local instance : UseRoundingPolicy RoundNearestEvenPolicy := ⟨⟩` +
  PolicyInstances); decode = `Fp.ofBits` computable; `fpExp` computable via `OpRefExec`
  interval kernels ⇒ softmax assemblable (exp/div gap CLOSED in principle); NO executable
  matvec/softmax/MLP (library layer = certificate structures, checkers write their own
  folds); no native floats anywhere ⇒ compiled = exact ℚ/ℤ bignum, ~0.5µs/scalar-op scale.
- **Checker** `Flean/Checker/ModAddReadout.lean`: `specLogit resid wU i j` = sequential
  spec-Binary32 (RNE) mul/add dot product of residual row i with `W_U` column j (128 steps,
  left-to-right, `Fp`-total so non-finites propagate); `ReadoutCorrect resid wU` = ∀ pair
  (a,b), true-class logit finite ∧ strictly > all 113 other logits by exact ℚ comparison of
  decoded values; `checkReadout : Array UInt32 → Array UInt32 → Bool` computes each row once
  (`rowLogits` via `Array.ofFn`) and checks; **`checkReadout_sound : checkReadout resid wU =
  true → ReadoutCorrect resid wU`** parametric over ALL word arrays (proof: `List.all_eq_true`
  + `Array.getD`-of-`ofFn` helper + match-split; no kernel data).
- **Accuracy bridge** `Flean/Checker/ModAddReadoutAccuracy.lean`: `realizedLogit` (ℝ-valued,
  junk 0 at non-finite) + `ReadoutCorrect → FailureSet (realizedLogit resid wU) = ∅` and
  `accuracy … = 1` in the kernel-pure `ModAddClock` framework. So the checker run lands
  directly in the established failure-set/accuracy vocabulary. (ReadoutCorrect is strictly
  stronger: also dominates the `'='` logit which ZMod-indexed FailureSet can't see.)
- **Honest trust statement**: residual stream = torch-exported data (trusted); unembed layer
  arithmetic = re-executed in Flean spec (not trusted); claim level = Lean compiler + file
  read, NOT kernel decide. Negative control passed: NaN-corrupting resid row 0 → checker
  flags non-finite label logit.
- **Gotchas**: (1) `local instance` doesn't export — name the instance (`instB32`) and
  re-attach with `attribute [local instance] instB32` in downstream files; keep Main
  instance-free via small helpers (`fpToRat?`). (2) NEVER let simp/whnf touch `specLogit`
  applied to symbolic args — the 128-step foldl explodes (deterministic whnf timeout);
  rewrite the match *scrutinee* with an equation lemma (`realizedLogit_of_finite` via
  `unfold` + `rw [hf]`) instead of `simp [realizedLogit, hf]`. (3) `Nat.Prime 113` by
  norm_num needs `import Mathlib.Tactic.NormNum.Prime` + `unfold p` first.
- **Run on seed-0 checkpoint (CONCRETE RESULT)**: `checkReadout = true` ⇒ `ReadoutCorrect`
  holds ⇒ (bridge) `accuracy (realizedLogit resid wU) = 1`. All 12769/12769 pairs correct;
  **exact-rational min Binary32 logit margin = 9.605161… (truncated)**, matching torch fp32
  9.6052 — first checker-certified concrete number about the real network. Report pass 861s +
  verified pass ≈854s (~67ms/row, exact ℚ bignum, single-threaded). Timing gotcha: a pure
  `let ok := checkReadout …` between two `IO.monoMsNow` reads got floated by the compiler to
  its first use (printed "0 ms"); force via println before reading the second clock (fixed in
  Main); actual duration recovered from log-file mtimes.
- **NEXT (shrink the trusted-activation boundary)**: recompute MLP (`W_out·relu(W_in·x+b_in)
  +b_out` — fpRelu certified, all ops exist) from post-attention residual; then attention
  (softmax via `fpExp`+`fpDivFinite` — survey says assemblable); each step moves the torch
  boundary one layer up until only embeddings are data. Also: margin-table emitter with
  soundness ("emitted q ≤ true margin"), frequency detection.

---

## STATUS (tracker)

Idealized clock decoder for `(a+b) mod p`, margin-centric, in `Flean/Operations/ModAddClock.lean`.

- [x] Mechanism: `phase`, `clockLogit` (frequency-set-parameterized).
- [x] Exact correctness: strict argmax (`clockLogit_lt_self`), `CorrectAt`, `correct_everywhere`.
- [x] Margin object (`margin`, `margin_pos`) + failure criterion (`correct_under_perturbation`).
- [x] Decoder = modular addition (`IsArgmax`, `isArgmax_iff_eq`, `clock_decodes_add`).
- [x] Failure set / accuracy as first-class objects; idealized 100% (`accuracy_clock_eq_one`).
- [x] Certified-accuracy bridge (`failureSet_subset_smallMargin`, `accuracy_eq_one_of_margin_gt`).
- [x] **#1 Single-frequency fragility**: `margin {k} s = 1 − cos(2π/p) ≤ 2π²/p²`; `1/p²` robustness
      threshold ⇒ redundancy imperative.
- [x] **#1b Multi-frequency margin growth** —
      `8|K|/p² ≤ |K|(1-cos(2π/p)) ≤ margin K s`.
- [x] **#2a FP readout integration** — `FiniteFp` feature/readout tables + `FpMatVecBound` execution;
      quantization/arithmetic error split; exact and algebraic failure-set certificates.
- [x] **#2b Binary32 tables** — full `p=113` nonzero bank, canonical RNE `FiniteFp` table, uniform
      entry error, explicit table quantization term, and algebraic margin threshold.
- [x] **#2c Upstream sum-feature construction** — compute the feature from separate rounded `a` and
      `b` embeddings using Binary32 product/FMA blocks.
- [x] **#2d First concrete accuracy number** — sequential 224-step Binary32 FMA readout with total
      error below the full-bank margin, proving end-to-end accuracy one at `p=113`.
- [x] **#2e Literal ingestion core** — checked finite Binary32 words, exact encode/decode round trip,
      certified literal vectors, `FpClockTables` conversion, and the complete exact zero row.
- [x] **#2f Full literal table artifact — superseded decision** — do not bulk-certify canonical trig rows as
      the main path; retain this only as an optional reference-backend artifact.
- [ ] **#2g Representation-first core** — approximate cyclic code with composition defect, score
      defect, arithmetic error, and margin; design it after inspecting a real checkpoint, then bridge
      the exact Fourier clock as a reference instance.
- [ ] **Concrete full-set margin** — `margin (univ.erase 0) s = p` via the root-of-unity sum
      (`∑_{k:ZMod p} cos(phase k m) = if m=0 then p else 0`; route `Complex.exp_ofReal_mul_I_re` +
      `geom_sum_eq`/`IsPrimitiveRoot.geom_sum_eq_zero` + ZMod→range bijection). Heavy; deferred.
- [x] **#3a Weights-into-Lean ingestion — done, then deliberately retired** (2026-07-21): full
      bit-exact literal ingestion shipped and kernel-certified (commit `f5e1062`), removed in
      `d0d3105` in favor of the verified-checker architecture (bulk data out of Lean).
- [~] **#3b Verified checkers** — WALKING SKELETON DONE 2026-07-21 (session 3 entry above):
      FLEANTEN interchange + `Flean/Checker/ModAddReadout.lean` (`checkReadout` recomputes the
      unembed layer in spec-Binary32 from torch-exported residuals, `checkReadout_sound`
      parametric) + accuracy bridge into `FailureSet`/`accuracy` + compiled run on the seed-0
      checkpoint. REMAINING: walk the recomputation upstream (MLP+ReLU → attention/softmax →
      embeddings) until only raw weights are data; analysis emitters (frequency subspaces,
      margin table, range certs, composition defect).
- [ ] **#4 RG / Wisp probe** — which frequencies survive FP precision (= relevant vs irrelevant
      operators, leak-as-truncation); frequency redundancy as √n error correction; may *explain* the
      sparse frequency count (FP can't resolve more).

**Discipline:** each step should produce a concrete number, say something about the real net, or be a
genuinely novel quantitative insight (#1 was). Resist proving more idealized margin formulas for their
own sake — the cathedral-admiring failure mode.
