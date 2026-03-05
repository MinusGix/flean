import Flean.Util
import Flean.Operations.RoundIntSig

/-! # Generic sticky cell extraction

Parametric machinery for extracting a sticky cell from rational brackets.
Given a function `bounds : ℕ → ℚ × ℚ` producing progressively tighter brackets
around a target value, this module provides:
- `stickyShift`: compute the bit shift from a positive rational lower bound
- `stickyExtract`: extract `(q, e_base)` from lower/upper bounds
- `stickyTryOne`: try one extraction at a given precision level
- `stickyExtractLoop`: iterate with fuel until cell agreement

These are independent of the operation being computed (exp, log, sin, etc.).
Operation-specific code provides:
1. A `bounds` function producing correct brackets at each iteration
2. A fuel bound guaranteeing termination
3. Bracket correctness proofs (`lower < target ≤ upper`)
-/

section StickyExtract

variable [FloatFormat]

/-! ## Output type -/

/-- Generic sticky cell output: quotient and base exponent. -/
structure StickyOut where
  q : ℕ
  e_base : ℤ
deriving Repr, DecidableEq

/-- Generic operation reference-kernel output.

Extends `StickyOut` with an `isExact` flag:
- `isExact = true` encodes exact branch with magnitude `2*q`.
- `isExact = false` encodes sticky branch with sticky index `q`. -/
structure OpRefOut where
  q : ℕ
  e_base : ℤ
  isExact : Bool
deriving Repr, DecidableEq

/-- Convert a sticky cell to an `OpRefOut` with `isExact := false`. -/
def StickyOut.toOpRefOut (s : StickyOut) : OpRefOut :=
  { q := s.q, e_base := s.e_base, isExact := false }

omit [FloatFormat] in
@[simp] theorem StickyOut.toOpRefOut_q (s : StickyOut) : s.toOpRefOut.q = s.q := rfl
omit [FloatFormat] in
@[simp] theorem StickyOut.toOpRefOut_e_base (s : StickyOut) : s.toOpRefOut.e_base = s.e_base := rfl
omit [FloatFormat] in
@[simp] theorem StickyOut.toOpRefOut_isExact (s : StickyOut) : s.toOpRefOut.isExact = false := rfl

/-! ## Shift and extraction -/

/-- Compute shift `s` from a positive rational, targeting `prec + 3` bits in `q`. -/
def stickyShift (r : ℚ) : ℕ :=
  let p := r.num.natAbs
  let d := r.den
  let targetBits := FloatFormat.prec.toNat + 4
  let s_int : ℤ := (targetBits : ℤ) + (Nat.log2 d : ℤ) - (Nat.log2 p : ℤ)
  s_int.toNat

/-- Extract `(q, e_base)` from a positive rational lower bound.

Uses `⌊lower · 2^s⌋` as `q` where `s = stickyShift lower`. -/
def stickyExtract (lower : ℚ) : StickyOut :=
  let s := stickyShift lower
  let p_lo := lower.num.natAbs
  let d_lo := lower.den
  let q := p_lo * 2 ^ s / d_lo
  let e_base : ℤ := -((s : ℤ)) - 1
  { q := q, e_base := e_base }

/-! ## Core q bound -/

/-- Core arithmetic: with the log2-based shift, `p * 2^s / d ≥ 2^(prec+3)`. -/
theorem initial_q_ge_minQ (p d : ℕ) (hp : 0 < p) (hd : 0 < d) :
    let s_int : ℤ := ((FloatFormat.prec.toNat + 4 : ℕ) : ℤ) +
      ((Nat.log2 d : ℕ) : ℤ) - ((Nat.log2 p : ℕ) : ℤ)
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s_int.toNat / d := by
  simp only
  set prec2 := FloatFormat.prec.toNat + 3
  set lp := Nat.log2 p
  set ld := Nat.log2 d
  set s_int : ℤ := ((prec2 + 1 : ℕ) : ℤ) + (ld : ℤ) - (lp : ℤ)
  set s := s_int.toNat
  have hp_ne : p ≠ 0 := by omega
  have hd_ne : d ≠ 0 := by omega
  have hlp : 2 ^ lp ≤ p := Nat.log2_self_le hp_ne
  have hdlt : d < 2 ^ (ld + 1) := (Nat.log2_lt hd_ne).mp (Nat.lt_succ_of_le (le_refl ld))
  rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
  by_cases hs : (0 : ℤ) ≤ s_int
  · have hlp_le : lp ≤ prec2 + 1 + ld := by omega
    have hs_eq : s = prec2 + 1 + ld - lp := by omega
    have key : 2 ^ (prec2 + 1 + ld) ≤ p * 2 ^ s := by
      calc 2 ^ (prec2 + 1 + ld)
          = 2 ^ (lp + (prec2 + 1 + ld - lp)) := by congr 1; omega
        _ = 2 ^ lp * 2 ^ (prec2 + 1 + ld - lp) := by rw [Nat.pow_add]
        _ ≤ p * 2 ^ s := by rw [hs_eq]; exact Nat.mul_le_mul_right _ hlp
    exact le_of_lt (calc 2 ^ prec2 * d
        < 2 ^ prec2 * 2 ^ (ld + 1) :=
          Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
      _ = 2 ^ (prec2 + 1 + ld) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ p * 2 ^ s := key)
  · push_neg at hs
    have hs_eq : s = 0 := Int.toNat_eq_zero.mpr (le_of_lt hs)
    rw [hs_eq, Nat.pow_zero, Nat.mul_one]
    have step1 : 2 ^ prec2 * d < 2 ^ (prec2 + ld + 1) := by
      calc 2 ^ prec2 * d < 2 ^ prec2 * 2 ^ (ld + 1) :=
            Nat.mul_lt_mul_of_pos_left hdlt (by positivity)
        _ = 2 ^ (prec2 + (ld + 1)) := by rw [← Nat.pow_add]
        _ = 2 ^ (prec2 + ld + 1) := by ring_nf
    have step2 : prec2 + ld + 1 ≤ lp := by omega
    exact le_of_lt (lt_of_lt_of_le step1
      (le_trans (Nat.pow_le_pow_right (by omega) step2) hlp))

/-- `stickyShift`-based q for a positive rational is ≥ 2^(prec+3). -/
theorem stickyShift_q_ge (r : ℚ) (hpos : 0 < r) :
    let p := r.num.natAbs
    let d := r.den
    let s := stickyShift r
    2 ^ (FloatFormat.prec.toNat + 3) ≤ p * 2 ^ s / d := by
  have hp : 0 < r.num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hpos))
  exact initial_q_ge_minQ r.num.natAbs r.den hp r.den_pos

/-- `stickyExtract` produces `q ≥ 2^(prec+2)` for positive lower bound. -/
theorem stickyExtract_q_ge (lower : ℚ) (hpos : 0 < lower) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (stickyExtract lower).q := by
  have hraw := stickyShift_q_ge lower hpos
  simp only at hraw
  simp only [stickyExtract]
  have : 2 ^ (FloatFormat.prec.toNat + 2) ≤ 2 ^ (FloatFormat.prec.toNat + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ## Parametric try-one and loop -/

/-- Try one extraction attempt at given precision level.
Returns `some result` if `⌊lower·2^s⌋ = ⌊upper·2^s⌋`, `none` otherwise. -/
def stickyTryOne (bounds : ℕ → ℚ × ℚ) (iter : ℕ) : Option StickyOut :=
  let (lower, upper) := bounds iter
  let result := stickyExtract lower
  let s := stickyShift lower
  let q_hi := upper.num.natAbs * 2 ^ s / upper.den
  if result.q = q_hi then some result
  else none

/-- Iterative sticky cell extraction. Refines precision until cell agreement. -/
def stickyExtractLoop (bounds : ℕ → ℚ × ℚ) (iter : ℕ) : ℕ → StickyOut
  | 0 => { q := 0, e_base := 0 }
  | fuel + 1 =>
    match stickyTryOne bounds iter with
    | some r => r
    | none => stickyExtractLoop bounds (iter + 1) fuel

/-! ## Loop properties -/

/-- When `stickyTryOne` succeeds, it produces q ≥ 2^(prec+2). -/
theorem stickyTryOne_q_ge (bounds : ℕ → ℚ × ℚ) (iter : ℕ) (r : StickyOut)
    (hr : stickyTryOne bounds iter = some r)
    (hpos : 0 < (bounds iter).1) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ r.q := by
  simp only [stickyTryOne] at hr
  split_ifs at hr with heq
  obtain rfl := Option.some.inj hr
  exact stickyExtract_q_ge _ hpos

/-- When `stickyTryOne` succeeds, q > 0. -/
theorem stickyTryOne_q_pos (bounds : ℕ → ℚ × ℚ) (iter : ℕ) (r : StickyOut)
    (hr : stickyTryOne bounds iter = some r)
    (hpos : 0 < (bounds iter).1) :
    0 < r.q := by
  have h1 := stickyTryOne_q_ge bounds iter r hr hpos
  have h2 : 0 < 2 ^ (FloatFormat.prec.toNat + 2) := Nat.pos_of_ne_zero (by positivity)
  omega

/-- The extraction loop: if q > 0, then q ≥ 2^(prec+2). -/
theorem stickyExtractLoop_q_ge (bounds : ℕ → ℚ × ℚ) (iter fuel : ℕ)
    (hpos : ∀ i, 0 < (bounds i).1)
    (hq : 0 < (stickyExtractLoop bounds iter fuel).q) :
    2 ^ (FloatFormat.prec.toNat + 2) ≤ (stickyExtractLoop bounds iter fuel).q := by
  induction fuel generalizing iter with
  | zero => simp [stickyExtractLoop] at hq
  | succ n ih =>
    simp only [stickyExtractLoop] at hq ⊢
    match hm : stickyTryOne bounds iter with
    | some r =>
      simp [hm] at hq ⊢
      exact stickyTryOne_q_ge bounds iter r hm (hpos iter)
    | none =>
      simp [hm] at hq ⊢
      exact ih (iter + 1) hq

/-- If some iteration succeeds, the loop returns positive q. -/
theorem stickyExtractLoop_pos_of_success (bounds : ℕ → ℚ × ℚ) (start fuel : ℕ)
    (hpos : ∀ i, 0 < (bounds i).1)
    (hsuccess : ∃ n, start ≤ n ∧ n < start + fuel ∧
      (stickyTryOne bounds n).isSome = true) :
    0 < (stickyExtractLoop bounds start fuel).q := by
  induction fuel generalizing start with
  | zero => obtain ⟨_, _, hlt, _⟩ := hsuccess; omega
  | succ fuel ih =>
    simp only [stickyExtractLoop]
    match hm : stickyTryOne bounds start with
    | some r =>
      simp
      exact stickyTryOne_q_pos bounds start r hm (hpos start)
    | none =>
      simp
      apply ih (start + 1)
      obtain ⟨n, hge, hlt, hn⟩ := hsuccess
      refine ⟨n, ?_, by omega, hn⟩
      by_cases h : n = start
      · subst h; simp [hm] at hn
      · omega

/-- If the loop encounters a successful `stickyTryOne` at any iteration, it returns that result. -/
theorem stickyExtractLoop_of_isSome (bounds : ℕ → ℚ × ℚ) (iter fuel : ℕ)
    (h : (stickyTryOne bounds iter).isSome)
    (hfuel : 0 < fuel) :
    stickyExtractLoop bounds iter fuel = (stickyTryOne bounds iter).get h := by
  match fuel, hfuel with
  | fuel + 1, _ =>
    simp only [stickyExtractLoop]
    have := Option.isSome_iff_exists.mp h
    obtain ⟨r, hr⟩ := this
    simp [hr]

/-! ## Sticky interval from bracket agreement -/

omit [FloatFormat] in
/-- If `lower < v ≤ upper` and both `⌊lower·2^s⌋ = ⌊upper·2^s⌋ = q`,
then `v ∈ (q·2^(-s), (q+1)·2^(-s))` i.e. `inStickyInterval q (-(s+1)) v`. -/
theorem inStickyInterval_of_bracket
    (lower upper : ℚ) (hl_pos : 0 < lower) (v : ℝ) (s : ℕ)
    (hv_lower : (lower : ℝ) < v)
    (hv_upper : v ≤ (upper : ℝ))
    (hq_agree : lower.num.natAbs * 2 ^ s / lower.den =
      upper.num.natAbs * 2 ^ s / upper.den) :
    let q := lower.num.natAbs * 2 ^ s / lower.den
    inStickyInterval (R := ℝ) q (-((s : ℤ)) - 1) v := by
  simp only
  set p_lo := lower.num.natAbs
  set d_lo := lower.den
  set p_hi := upper.num.natAbs
  set d_hi := upper.den
  set q := p_lo * 2 ^ s / d_lo
  have hd_lo : 0 < d_lo := lower.den_pos
  have hd_hi : 0 < d_hi := upper.den_pos
  have h2s_pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hu_pos : 0 < upper := lt_of_lt_of_le hl_pos (by exact_mod_cast le_of_lt (lt_of_lt_of_le hv_lower hv_upper))
  have hq_le_lower : (q : ℝ) / (2 : ℝ) ^ s ≤ (lower : ℝ) := by
    rw [div_le_iff₀ h2s_pos, Rat.cast_eq_natAbs_div_den lower hl_pos, div_mul_eq_mul_div,
      le_div_iff₀ (Nat.cast_pos.mpr hd_lo)]
    exact_mod_cast nat_floor_div_mul_le p_lo d_lo s
  have hupper_lt : (upper : ℝ) < ((q : ℝ) + 1) / (2 : ℝ) ^ s := by
    rw [lt_div_iff₀ h2s_pos, Rat.cast_eq_natAbs_div_den upper hu_pos, div_mul_eq_mul_div,
      div_lt_iff₀ (Nat.cast_pos.mpr hd_hi)]
    have hq_eq : q = p_hi * 2 ^ s / d_hi := hq_agree
    rw [hq_eq]
    exact_mod_cast real_lt_nat_floor_div_succ_mul p_hi d_hi s hd_hi
  constructor
  · rw [two_mul_zpow_neg_succ, show (q : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) =
      (q : ℝ) / (2 : ℝ) ^ s from by rw [zpow_neg, zpow_natCast]; ring]
    exact lt_of_le_of_lt hq_le_lower hv_lower
  · rw [two_mul_zpow_neg_succ, show ((q : ℝ) + 1) * (2 : ℝ) ^ (-(s : ℤ)) =
      ((q : ℝ) + 1) / (2 : ℝ) ^ s from by rw [zpow_neg, zpow_natCast]; ring]
    exact lt_of_le_of_lt hv_upper hupper_lt

/-! ## Generic loop soundness -/

/-- When `stickyTryOne` succeeds and the bounds bracket the target,
the result is in the correct sticky interval. -/
theorem stickyTryOne_sound (bounds : ℕ → ℚ × ℚ) (iter : ℕ) (r : StickyOut)
    (v : ℝ)
    (hr : stickyTryOne bounds iter = some r)
    (hv_lower : ((bounds iter).1 : ℝ) < v)
    (hv_upper : v ≤ ((bounds iter).2 : ℝ))
    (hl_pos : 0 < (bounds iter).1) :
    inStickyInterval (R := ℝ) r.q r.e_base v := by
  simp only [stickyTryOne] at hr
  split_ifs at hr with heq
  obtain rfl := Option.some.inj hr
  exact inStickyInterval_of_bracket (bounds iter).1 (bounds iter).2 hl_pos v
    (stickyShift (bounds iter).1) hv_lower hv_upper heq

/-- When the loop finds a result and all iterations bracket the target,
the result satisfies `inStickyInterval`. -/
theorem stickyExtractLoop_sound (bounds : ℕ → ℚ × ℚ) (iter fuel : ℕ) (v : ℝ)
    (hpos : ∀ i, 0 < (bounds i).1)
    (hv_lower : ∀ i, ((bounds i).1 : ℝ) < v)
    (hv_upper : ∀ i, v ≤ ((bounds i).2 : ℝ))
    (hq : 0 < (stickyExtractLoop bounds iter fuel).q) :
    inStickyInterval (R := ℝ) (stickyExtractLoop bounds iter fuel).q
      (stickyExtractLoop bounds iter fuel).e_base v := by
  induction fuel generalizing iter with
  | zero => simp [stickyExtractLoop] at hq
  | succ n ih =>
    simp only [stickyExtractLoop] at hq ⊢
    match hm : stickyTryOne bounds iter with
    | some r =>
      simp [hm] at hq ⊢
      exact stickyTryOne_sound bounds iter r v hm (hv_lower iter) (hv_upper iter) (hpos iter)
    | none =>
      simp [hm] at hq ⊢
      exact ih (iter + 1) hq

/-! ## Generic reference-kernel classes

Parametric execution and soundness contracts for any operation whose
reference kernel produces an `OpRefOut`. The target function
`target : FiniteFp → ℝ` gives the positive magnitude of the exact result. -/

/-- Computable reference-kernel execution hook, parametric over the target function. -/
class OpRefExec (target : FiniteFp → ℝ) where
  run : FiniteFp → OpRefOut

/-- Soundness contract for a computable reference kernel.

The `target` function returns the *positive magnitude* of the exact result.
Sign handling is part of the operation-specific layer. -/
class OpRefExecSound (target : FiniteFp → ℝ) [OpRefExec target] : Prop where
  exact_mag_ne_zero :
    ∀ (a : FiniteFp) (o : OpRefOut),
      OpRefExec.run (target := target) a = o →
      o.isExact = true →
      (2 * o.q) ≠ 0
  exact_value :
    ∀ (a : FiniteFp) (o : OpRefOut),
      OpRefExec.run (target := target) a = o →
      o.isExact = true →
      intSigVal (R := ℝ) false (2 * o.q) o.e_base = target a
  sticky_q_lower :
    ∀ (a : FiniteFp) (o : OpRefOut),
      OpRefExec.run (target := target) a = o →
      o.isExact = false →
      2 ^ (FloatFormat.prec.toNat + 2) ≤ o.q
  sticky_interval :
    ∀ (a : FiniteFp) (o : OpRefOut),
      OpRefExec.run (target := target) a = o →
      o.isExact = false →
      inStickyInterval (R := ℝ) o.q o.e_base (target a)

end StickyExtract
