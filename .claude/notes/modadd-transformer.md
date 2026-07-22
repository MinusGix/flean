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

### Added 2026-07-21 (session 4 of the day) — SECOND RUNG: MLP + unembed checker

Trusted-activation boundary moved one layer up: torch now only supplies embeddings +
attention (`resid_mid`, added to `export_activations.py`); MLP and unembed are re-executed
in the Lean spec. `Flean/Checker/ModAddMlp.lean`:

- Spec: `seqDot` (generic sequential RNE dot), `mlpHidden` = `fpRelu (fpAdd ⟨W_in row, x⟩
  b_in)`, `mlpOut` = `(x_d + ⟨W_out row, h⟩) + b_out_d`, `mlpLogit` = `⟨out, W_U col⟩`;
  `MlpReadoutCorrect` (strict argmax, exact ℚ).
- Exec: memoized stages `hiddenArr`/`outArr`/`rowLogitsMlp` (each neuron/coordinate once per
  row; named defs + let-sharing, NOT inline — inlining hiddenArr into the closure would
  recompute it 512×), `checkRowsForA`, **`checkMlpReadout` = per-`a` `Task` fan-out**;
  reporting helpers `rowMargin`/`foldMargin` live here (Main must stay instance-free).
- Soundness: `checkMlpReadout_sound` parametric; Task layer proof-transparent via
  `get_spawn_const : (Task.spawn fun _ => x).get = x := rfl` (state it with the body as a
  VARIABLE; transporting the concrete body by defeq = whnf explosion). Pointwise lemmas via
  rfl-zeta-equations + `getD_ofFn'` (eta-clean g, avoids `f ⟨j,hj⟩` beta-redex residue that
  breaks later `rw`s) + `seqDot_congr` (foldl-over-range induction). `congr 2` on fpAdd goals
  = max-recursion (instance-heavy implicits); targeted `rw` of the differing seqDot subterm
  instead.
- Accuracy bridge refactored GENERIC: `ArgmaxCorrect L` + `realizedOf L` +
  `failureSet_realizedOf_eq_empty`/`accuracy_realizedOf_eq_one` proved once;
  `ReadoutCorrect ↔ ArgmaxCorrect (specLogit …)` and MLP version are `Iff.rfl`;
  headline `accuracy_realizedMlp_eq_one`.
- **Run (seed-0 checkpoint): `checkMlpReadout = true`, 12769/12769; exact-rational min
  Binary32 margin = 9.605161… — identical to the readout rung to all 6 printed digits**
  (min-margin row's logits barely touched by MLP-recompute-vs-torch order differences);
  per-row margins differ from torch in the ~4th decimal as expected. Report pass 1045s +
  verified pass 1052s at ~14.5 cores (~530 ms/row serial, 16 hw threads, `Task` per outer
  `a`). Negative controls: NaN in resid_mid[5,0] propagates → rejected; single mantissa-bit
  flip (0.067→0.098) absorbed by margin → legitimate accept.
- NEXT rung: attention (per-head QK scores, causal mask, softmax via `fpExp`+`fpDivFinite`,
  OV mix) then embeddings — after that only raw weight tensors are data. Attention softmax
  spec-fidelity question to settle first: torch computes `scores/√32` and `-1e10` masking;
  our spec must fix exact Binary32 constants and orders for these.

### Added 2026-07-21 (session 5 of the day) — FINAL RUNG: FULL FORWARD PASS FROM RAW WEIGHTS

**THE CAPSTONE EXTENSIONAL RESULT.** `Flean/Checker/ModAddFull.lean`: no torch activations
remain — the eleven raw weight tensors (`Weights` structure) are the only data. Attention
folded in AND embeddings (trivial: `W_E` column + `W_pos` add), so this went straight from
"MLP rung" to "whole network" in one file.

- **Spec decisions** (ours, not bit-matching torch; drift vs torch irrelevant given margin):
  score scale = `fpDiv` by `sqrt32 := decode 0x40b504f3` (Binary32 nearest √32, what torch
  uses); causal mask VACUOUS at readout position (q=2 attends to all 3 positions — check
  `tril` row 2 = ones) so it never appears; softmax = max-subtracted (`fpMax2` NaN-propagating
  via toRat comparison) then `fpExp`/sequential-add denom/`fpDiv`. `fpExp` computable via
  `OpRefExec expTarget` (import `ExpComputableDefs`, priority 500 instance beats the
  noncomputable 120 one; verified exp(−1.5) → `0x3e647c3c` correctly rounded).
- Spec chain `xEmb→kRow/vRow/qRow→score→smax/expScore/denom/attnW→zRow→attnOutF→residMidF→
  hiddenF→outF→fullLogit`; `FullNetCorrect W`. Exec: NINE memoized stages (qArr, scoreArr,
  expArr, attnArr [12 entries flat `e=i*nPos+pos`], zArr, midArr, hid, out, logits); k/v rows
  used exactly once ⇒ deliberately NOT memoized (inline in score/z entries). Per-`a` Task
  fan-out; `checkFullNet_sound` parametric over all Weights.
- **Proof gotchas new this rung**: (1) omega treats named constants (`nPos` etc.) as OPAQUE
  ATOMS — `have h : nPos = 3` doesn't help; must `simp only [nPos_eq, …] at hyps ⊢` to
  literals BEFORE omega (div/mod by literals then fine). (2) `rw [show x = x+0 from rfl]`
  to make `i*nPos` match a lemma's `i*nPos+0` REWRITES INSIDE `+1`/`+2` terms too (subterm
  capture) — write a separate pos-0 lemma (`scoreArrD_getD0` via `simpa`) instead. (3)
  `congr 1` on `fpDiv (seqDot …) c = fpDiv (seqDot …) c` hit max recursion — prove the
  seqDot equality as `have hs` (via seqDot_congr) and `rw [hs]`. (4) index-flattening
  lemmas stated with output `f (e / nPos) (e % nPos)` compose cleanly; derive `getD'`
  (i,pos) versions by omega div/mod rewrites.
- **Accuracy bridge**: `fullLogitRow W i j := fullLogit W (i/p) (i%p) j` +
  `fullNetCorrect_argmax` ((a*p+b)/p=a needs `simp only [hp] at hb ⊢; omega`) ⇒
  `accuracy_realizedFull_eq_one`.
- **RUN (seed-0 checkpoint): `checkFullNet = true` — 12769/12769; exact-rational min
  Binary32 margin 9.605159…** (readout/MLP rungs: 9.605161; torch fp32: 9.6052 — the whole
  attention+softmax recompute in our op order moves the min margin by < 2·10⁻⁶). Report
  pass 2384s + verified pass 2378s (~40 min each, ~14.5 cores; ~1.2 s/row serial = ~280k
  spec mul/adds + 12 fpExp per row; ~3.6G bignum spec ops/pass). Spot margins: row 0
  17.686193 (MLP rung 17.686199). Negative control: NaN in W_in[0,0] → all rows non-finite
  → rejected.
- **Statement achieved**: `checkFullNet W = true → FullNetCorrect W` (parametric theorem) +
  compiled run on the on-disk checkpoint ⇒ *the actual Nanda grokked network, as a Binary32
  program under Flean's IEEE spec, computes (a+b) mod 113 on every input with margin ≥
  9.605159* — trust = Lean compiler + FLEANTEN file read, honestly stated. Extensional half
  of #3b COMPLETE. Remaining: mechanism/representation certificates (#2g), analysis emitters,
  and (if scaling ever matters) verified fast bit-level kernels via IntegerEquivalence
  (~100-1000× speedup path).

### Session 6 (2026-07-21/22) — checker performance: PROFILED, two hypotheses killed

Motivation: full pass = ~40 min × 2 on 14.5 cores, so any precision/frequency sweep (#4)
is unaffordable. User chose the `@[csimp]` mechanism (prove `fast = spec` as functions,
tag csimp ⇒ compiled code swaps, **`checkFullNet_sound` and all definitions untouched**;
caveat: csimp does NOT affect kernel reduction / `decide` / `native_decide`).

**Measure, don't hypothesize — twice bitten this session:**
- `perf` on the readout path: >50% of runtime is `malloc`/`cfree`/`realloc` + GMP
  (`__gmpz_n_pow_ui` 9.5%, `__gmpz_add`, `__gmpz_mul_2exp`, `lp_mathlib_Nat_clog_go` 4.6%).
  Almost none is arithmetic.
- **KILLED HYPOTHESIS 1 — exact alignment in `fpAddFinite`.** `Flean/Operations/Add.lean:28`
  aligns both significands to `e_min` *exactly* (`a.m * 2^(a.e - e_min).toNat`), which looked
  like the bignum source; I designed a guard/round/sticky theorem (cap shift at `prec+3`,
  sticky-OR the discarded bits) to fix it. Built it and measured: **249 ms → 227 ms, only 5%.**
  In these dot products the weights are all the same order of magnitude, so the exponent
  spread rarely exceeds `prec+3` and exact alignment almost never does a big shift.
  (The capped variant *was* correct — 64/64 dot products bit-identical — just pointless here.
  Do not spend days proving the sticky-bit theorem for this workload.)
- **REAL CULPRIT — `decode`.** Per-element costs over 51,200 mul+add pairs:
  decode **1.7 µs**, fpMul ~0.3 µs, fpAdd ~0.27 µs. (`decode+mul` at 187 ms does *two*
  decodes = 172 ms, so multiplication is only ~15 ms.) Decode is ~90% of runtime.
  Cause: `decode w = Fp.ofBits ⟨w.toBitVec⟩` re-derives everything per call —
  `FloatBits.toBitsTriple` uses `BitVec.extractLsb'` (Nat shift + `% 2^n` → GMP alloc), and
  `isNaN`/`isInfinite` are **Props** decided through `BitVec.allOnes` comparisons.
  The checker pays this 12769× per weight word.
- Two fixes, same ~5-6×: (a) hoist decode out of the inner loop (measured **predecoded dot
  43 ms vs 249 ms = 5.8×**, needs ~12 stage rewrites + `Array.getD_map` congruences), or
  (b) **`decodeFast` on native UInt32 ops + `@[csimp] decode = decodeFast`** — ONE theorem,
  no restructuring, reusable Encoding result. Chose (b).
- After decode is fixed the residue is real `FiniteFp` arithmetic at ~0.84 µs/(mul+add),
  still ~400× off native ⇒ that is where packed-`UInt64` kernels (IntegerEquivalence) earn
  their keep. Ladder: **decode (≈5×, cheap) → packed kernels (remaining runway)**.
- Scratch harness: `Checker/BenchAdd.lean` + `bench_add` lean_exe in `lakefile.toml`
  (untracked). Measures decode / mul / add / predecoded separately. csimp effects are only
  visible in the compiled exe, so this is the correct measuring instrument.

**SHIPPED — `@[csimp] decode_eq_decodeFast`** (`Flean/Checker/ModAddReadout.lean`, new
`section DecodeFast` between `decode` and `specLogit`). `decodeFast` = native UInt32
shifts/masks; fully proved, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on
both it and `checkFullNet_sound`; full `lake build` clean; diff is **purely additive**
(`decode`'s definition and every existing theorem byte-for-byte unchanged).
- Measured (idle machine, best of 3): **decode 92 ms → ~1 ms (~90×)**; full dot product
  **249 ms → 45 ms (5.5×)**. `predecoded dot` (45 ms) now equals the plain dot ⇒ decode is
  free, so the *hoisting* option (a) is moot — don't bother implementing it.
- End-to-end `--layer full`, BOTH passes re-run and confirmed: report 608 s + verified 609 s
  = **1217 s vs 4762 s baseline (3.9×)**; `12769/12769`; **`checkFullNet = true`**; min margin
  **9.605159 — bit-identical to the pre-change value**. (Report pass measured 542 s on an idle
  machine, so ~4× is the fair figure.) Differential test of csimp'd decode vs untouched
  `Fp.ofBits`: 305,120 words, 0 mismatches.
- GOTCHAS: (1) **csimp placement is load-bearing** — it only rewrites declarations compiled
  *after* the attribute is registered, so the section must sit before `specLogit`/`rowLogits`,
  not at end of file. (2) `decodeFast` needs `dite` at BOTH branch levels; a plain `if` on the
  exponent-zero test leaves `¬(e = 0)` out of scope and the subnormal-vs-normal
  `IsValidFiniteVal` obligation becomes unprovable. (3) write `8388608`, not `2^23` — the
  latter compiles to a runtime `Nat.pow` call in the hot path. (4) `exponentBias` is not a
  separate `FloatFormat` field; it is `max_exp` (=127 for B32).
- NEXT RUNG: `fpAdd` is now the bottleneck (dot ≈ predecoded dot ≈ 45 ms for 51,200
  mul+add = ~0.9 µs/pair, still ~400× off native). That is the packed-`UInt64` kernel work
  (IntegerEquivalence) — same `@[csimp]` mechanism, but a real bit-level RNE proof.
  OPEN QUESTION for user: whether exhaustive sweeps are needed at all, or whether sampled
  sweeps + one exhaustive final run make the packed kernels lower priority than #2g.

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
- [~] **#2g Representation-first core** — approximate cyclic code with composition defect, score
      defect, arithmetic error, and margin; design it after inspecting a real checkpoint, then bridge
      the exact Fourier clock as a reference instance.
      **NUMERICAL DESIGN PASS DONE 2026-07-22** — `references/analyze_clock.py`,
      writeup `docs/clock_representation_analysis.md`. Headlines: freqs {14,35,41,42,52} carry
      **100.00%** of non-DC power (K=6/8 move defect by 0.026 — nothing spectral left);
      ideal clock margin **18.30** vs realized **9.605**, i.e. **the defect eats ~47% of the
      ideal margin**, almost all of it *composition* defect (12.01 = logits are not a function
      of a+b alone), NOT missing frequencies; **global sup-norm certificate is impossible at
      every K** (`margin − 2ε = −6.5`), only per-input works — symmetric per-input bound
      certifies 12584/12769 (**98.55%**), sharp correct-vs-wrong bound 12769/12769 (100%,
      min slack +0.1616). CAVEAT: the sharp bound uses realized defects ⇒ decomposition, not
      compression; a self-contained certificate needs defect bounds derived from the *weights*.
      That is the real open problem. RICHER MODELS DON'T HELP (`analyze_clock_plus.py`):
      clock+u[a,c]+v[b,c] holds only 1.01% extra power, cuts defect 12.41->10.58 but drops the
      model margin 18.30->13.05, so the GLOBAL certificate gets *worse*; per-input only
      98.55%->99.62%, at the cost of mechanistic meaning. Defect is diffuse + sup-norm-outlier
      driven, NOT missing structure (96.32% of power is already clock). Settled on K=5.
      **LEAN SHIPPED — `Flean/Operations/ModAddRepresentation.lean`** (sorry-free, axiom-clean,
      wired into `Flean/Operations.lean`): abstraction is a *cyclic kernel* `g : ZMod p -> R`
      with `kernelScore g s c = g (s - c)` — exactly the "depends only on a+b-c" class, and
      `clockLogit K = kernelScore (clockKernel K)` holds by `rfl`. Contents: `kernelMargin`,
      `kernelScore_le_of_ne`, `correct_of_defect` (per-input), `correct_of_defect_sharp`
      (per-class radii; the form that certifies 100% with min slack +0.16),
      `failureSet_subset_largeDefect`, `accuracy_ge_of_failureSet_subset`,
      `accuracy_ge_of_defect`, `accuracy_eq_one_of_defect`, plus the exact clock as the
      vanishing-defect instance (`kernelMargin_clockKernel_pos`, `clock_correct_of_defect`).
      Gotcha: `div_le_div_of_nonneg_right` has a different signature than expected — use
      `gcongr` for `a/c <= b/c`.
      STILL OPEN (the actual hard part): defect bounds derived from the WEIGHTS rather than
      measured — i.e. bound the off-diagonal power of `W_U . MLP` on the post-attention
      residual. Nonlinear (ReLU); not a short proof.
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
      checkpoint. SECOND RUNG DONE same day (session 4 entry): MLP+ReLU+unembed recomputed in
      spec (`ModAddMlp.lean`, Task-parallel, `checkMlpReadout = true`, min margin 9.605161).
      **FINAL RUNG DONE same day (session 5 entry): FULL forward pass from raw weights only
      (`ModAddFull.lean`, embeddings+attention+softmax+MLP+unembed all in spec;
      `checkFullNet = true`, 12769/12769, min margin 9.605159). EXTENSIONAL HALF COMPLETE.**
      REMAINING: analysis emitters (frequency subspaces, margin table, range certs,
      composition defect) feeding #2g; optional verified fast bit-level kernels
      (IntegerEquivalence pattern) if scaling matters.
- [ ] **#4 RG / Wisp probe** — which frequencies survive FP precision (= relevant vs irrelevant
      operators, leak-as-truncation); frequency redundancy as √n error correction; may *explain* the
      sparse frequency count (FP can't resolve more).

**Discipline:** each step should produce a concrete number, say something about the real net, or be a
genuinely novel quantitative insight (#1 was). Resist proving more idealized margin formulas for their
own sake — the cathedral-admiring failure mode.
