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
- [ ] **#2 First concrete accuracy number** — FP forward-error `δ` on `clockLogit` (the actual float
      readout, via `FpDotProductBound`/`AffineFormVec`), combined with a margin bound.
- [ ] **#1b Multi-frequency margin growth** — `margin {K} s` grows with `|K|` (the √n redundancy
      payoff; the complement of single-frequency fragility). Hard direction (Dirichlet/sparse sums).
- [ ] **Concrete full-set margin** — `margin (univ.erase 0) s = p` via the root-of-unity sum
      (`∑_{k:ZMod p} cos(phase k m) = if m=0 then p else 0`; route `Complex.exp_ofReal_mul_I_re` +
      `geom_sum_eq`/`IsPrimitiveRoot.geom_sum_eq_zero` + ZMod→range bijection). Heavy; deferred.
- [ ] **#3 Weights-into-Lean bridge** — concrete `FiniteFp` weight matrices + forward pass. The
      gating step that converts "idealized algorithm" into "the actual trained network".
- [ ] **#4 RG / Wisp probe** — which frequencies survive FP precision (= relevant vs irrelevant
      operators, leak-as-truncation); frequency redundancy as √n error correction; may *explain* the
      sparse frequency count (FP can't resolve more).

**Discipline:** each step should produce a concrete number, say something about the real net, or be a
genuinely novel quantitative insight (#1 was). Resist proving more idealized margin formulas for their
own sake — the cathedral-admiring failure mode.
