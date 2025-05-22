import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.LiftLets

import Flean.Basic

section Rounding

variable {R : Type*} [LinearOrderedField R] [FloorSemiring R] [OfNat R n]

-- TODO: should this be more central as a type rather than a one-off for bracketing pairs?
-- Possibly non-valid finite fp
@[ext]
structure QFiniteFp [FloatFormat] where
  /-- The sign of the number. -/
  s : Bool
  /-- The exponent -/
  e : ℤ
  /-- The integral significand. Without the sign. -/
  m : ℕ
  /-- Whether the number is exactly representable. -/
  guard: Bool
  sticky: Bool
  is_exact : Bool
deriving Repr

namespace QFiniteFp

variable [FloatFormat]

instance : Zero QFiniteFp :=
  ⟨{
    s := false,
    e := FloatFormat.min_exp,
    m := 0,
    guard := false,
    sticky := false
    is_exact := true,
  }⟩

@[simp]
theorem zero_def : (0 : QFiniteFp) = ⟨false, FloatFormat.min_exp, 0, false, false, true⟩ := rfl

end QFiniteFp

-- def bracketingPair_handleSubnormals [FloatFormat] (x : R) (e : ℤ) (z1 z2 : QFiniteFp) (is_exact : Bool)  : (QFiniteFp × QFiniteFp) :=
--   if e < FloatFormat.min_exp then
--     let shift := FloatFormat.min_exp - e
--     let z1 := denormalize z1 shift
--     let z2 := if is_exact then z2 else denormalize z2 shift
--     (z1, z2)
--   else
--     (z1, z2)

-- def bracketingPair_handleLargeSignificands [FloatFormat] (z1 z2 : QFiniteFp) (is_exact : Bool) : (QFiniteFp × QFiniteFp) :=
--   if z1.m ≥ (2 : R)^(FloatFormat.prec : ℤ) || (!is_exact && z2.m ≥ (2 : R)^(FloatFormat.prec : ℤ)) then
--     let z1 := normalize z1
--     if !is_exact then
--       let z2 := normalize z2
--       (z1, z2)
--     else
--       (z1, z2)
--   else
--     (z1, z2)

-- Based off of "An Implementation Guide to a Proposed Standard for Floating-Point Arithmetic" by Jerome T. Coonen
def bracket [FloatFormat] (x : R) : (QFiniteFp × QFiniteFp) :=
  if x = 0 then (0, 0)
  else
  let sign: Bool := x < 0
  -- 2^e <= |x| < 2^(e + 1)
  let e : ℤ := Int.log 2 (|x|)
  let e_eff : ℤ := max e FloatFormat.min_exp


  let M_real : R := |x| / (2 : R)^(e_eff - FloatFormat.prec + 1)

  let m_floor : ℕ := ⌊M_real⌋₊
  let m_ceil : ℕ := ⌈M_real⌉₊

  let is_exact : Bool := M_real == (m_floor : R) --m_floor == m_ceil

  let midpoint : R := (m_floor : R) + 0.5;
  let guard : Bool := if is_exact then false else M_real >= midpoint -- is the value in the upper half
  let sticky : Bool := if is_exact then false else M_real != midpoint -- is the value not exactly halfway

  let m1_final := m_floor
  let e1_final := e_eff
  let m2_final := if m_ceil == (2 : R)^(FloatFormat.prec : ℤ) then m_ceil / 2 else m_ceil
  let e2_final := if m_ceil == (2 : R)^(FloatFormat.prec : ℤ) then e_eff + 1 else e_eff

  let z1 := QFiniteFp.mk sign e1_final m1_final guard sticky is_exact
  let z2 := QFiniteFp.mk sign e2_final m2_final guard sticky is_exact
  (z1, z2)

def lowerBracket [FloatFormat] (x : R) : QFiniteFp :=
  if x = 0 then 0
  else
  let sign: Bool := x < 0
  -- 2^e <= |x| < 2^(e + 1)
  let e : ℤ := Int.log 2 (|x|)
  let e_eff : ℤ := max e FloatFormat.min_exp


  let M_real : R := |x| / (2 : R)^(e_eff - FloatFormat.prec + 1)

  let m_floor : ℕ := ⌊M_real⌋₊

  let is_exact : Bool := M_real == (m_floor : R)

  let midpoint : R := (m_floor : R) + 0.5;
  let guard : Bool := if is_exact then false else M_real >= midpoint -- is the value in the upper half
  let sticky : Bool := if is_exact then false else M_real != midpoint -- is the value not exactly halfway

  let m1_final := m_floor
  let e1_final := e_eff

  QFiniteFp.mk sign e1_final m1_final guard sticky is_exact

def upperBracket [FloatFormat] (x : R) : QFiniteFp :=
  if x = 0 then 0
  else
  let sign: Bool := x < 0
  -- 2^e <= |x| < 2^(e + 1)
  let e : ℤ := Int.log 2 (|x|)
  let e_eff : ℤ := max e FloatFormat.min_exp


  let M_real : R := |x| / (2 : R)^(e_eff - FloatFormat.prec + 1)

  let m_floor : ℕ := ⌊M_real⌋₊
  let m_ceil : ℕ := ⌈M_real⌉₊

  let is_exact : Bool := M_real == (m_floor : R) --m_floor == m_ceil

  let midpoint : R := (m_floor : R) + 0.5;
  let guard : Bool := if is_exact then false else M_real >= midpoint -- is the value in the upper half
  let sticky : Bool := if is_exact then false else M_real != midpoint -- is the value not exactly halfway

  let m2_final := if m_ceil == (2 : R)^(FloatFormat.prec : ℤ) then m_ceil / 2 else m_ceil
  let e2_final := if m_ceil == (2 : R)^(FloatFormat.prec : ℤ) then e_eff + 1 else e_eff

  QFiniteFp.mk sign e2_final m2_final guard sticky is_exact

theorem bracket_eq_lower [FloatFormat] (x : R) : (bracket x).1 = lowerBracket x := by
  unfold bracket lowerBracket
  simp_all only [Prod.mk_zero_zero, beq_iff_eq, ge_iff_le, Bool.if_false_left, zpow_natCast]
  split
  next h =>
    subst h
    simp_all only [Prod.fst_zero]
  next h => simp_all only

theorem bracket_eq_upper [FloatFormat] (x : R) : (bracket x).2 = upperBracket x := by
  unfold bracket upperBracket
  simp_all only [Prod.mk_zero_zero, beq_iff_eq, ge_iff_le, Bool.if_false_left, zpow_natCast]
  split
  next h =>
    subst h
    simp_all only [Prod.snd_zero]
  next h => simp_all only

@[simp]
theorem lowerBracket_neg_iff [FloatFormat] (x : R) : (lowerBracket x).s = true ↔ x < 0 := by
  unfold lowerBracket
  constructor
  · intro h
    split_ifs at h with h_1
    · simp_all only [decide_eq_true_eq]
  · intro h
    simp_all only [Prod.mk_zero_zero, decide_true, beq_iff_eq, ge_iff_le, Bool.if_false_left, zpow_natCast]
    split
    next h_1 =>
      subst h_1
      simp_all only [lt_self_iff_false]
    next h_1 => simp_all only

@[simp]
theorem upperBracket_neg_iff [FloatFormat] (x : R) : (upperBracket x).s = true ↔ x < 0 := by
  unfold upperBracket
  constructor
  · intro h
    split_ifs at h with h_1
    · simp_all only [decide_eq_true_eq]
  · intro h
    simp_all only [Prod.mk_zero_zero, decide_true, beq_iff_eq, ge_iff_le, Bool.if_false_left, zpow_natCast]
    split
    next h_1 =>
      subst h_1
      simp_all only [lt_self_iff_false]
    next h_1 => simp_all only

-- #eval @bracketingPair ℚ _ _ FloatFormat.Binary32.toFloatFormat _ ((2^(-(150 : ℤ))) : ℚ)
-- TODO: proof that if the number is exactly representable then the returned pair is just (num, num)

@[ext] structure FloatFlags where
  invalidOperation : Bool := false
  divisionByZero   : Bool := false
  overflow         : Bool := false
  underflow        : Bool := false
  inexactResult    : Bool := false
  -- Potential method to combine flags using OR
  def merge (f1 f2 : FloatFlags) : FloatFlags :=
    { invalidOperation := f1.invalidOperation || f2.invalidOperation,
      divisionByZero   := f1.divisionByZero   || f2.divisionByZero,
      overflow         := f1.overflow         || f2.overflow,
      underflow        := f1.underflow        || f2.underflow,
      inexactResult    := f1.inexactResult    || f2.inexactResult }


structure RoundResult [FloatFormat] where
  value : Option Fp
  flags : FloatFlags


/-- Round toward negative infinity -/
@[reducible]
def roundDownᵣ [FloatFormat] (x : R) : RoundResult :=
  let z := lowerBracket x
  let overflow : Bool := z.e > FloatFormat.max_exp
  let inexactResult : Bool := !z.is_exact || overflow
  let value : Fp := if overflow then
    if z.s then
      Fp.infinite true
    else
      Fp.finite FiniteFp.largestFiniteFloat
  else
  -- TODO: are we forgetting to set underflow flag?
    let is_subnormal : Bool := z.e == FloatFormat.min_exp && z.m > 0 && z.m < (2 : ℕ)^(FloatFormat.prec - 1)
    let underflow : Bool := is_subnormal && inexactResult
    let valid_finite := sorry
    Fp.finite (FiniteFp.mk z.s z.e z.m valid_finite)
  ⟨
    value,
    {
      inexactResult := inexactResult
      overflow := overflow
    }
  ⟩

@[reducible]
def roundDownᵣ' [FloatFormat] (x : R) : Option Fp :=
  let z := lowerBracket x
  let overflow := z.e > FloatFormat.max_exp
  let inexactResult := !z.is_exact || overflow
  if overflow then
    if z.s then
      Fp.infinite true
    else
      Fp.finite FiniteFp.largestFiniteFloat
  else
    let is_subnormal := z.e == FloatFormat.min_exp && z.m > 0 && z.m < (2 : ℕ)^(FloatFormat.prec - 1)
    let underflow := is_subnormal && inexactResult
    let valid_finite := sorry
    Fp.finite (FiniteFp.mk z.s z.e z.m valid_finite)

theorem roundDownᵣ_eq' [FloatFormat] (x : R) : (roundDownᵣ x).value = roundDownᵣ' x := by
  unfold roundDownᵣ roundDownᵣ'
  simp_all only [gt_iff_lt, decide_eq_true_eq, lowerBracket_neg_iff]
  split
  next h =>
    split
    next h_1 => simp_all only
    next h_1 => simp_all only [not_lt]
  next h => simp_all only [not_lt]

/-- Round toward negative infinity -/
@[reducible]
def roundDownₓ [FloatFormat] (x : R) : Fp :=
  (roundDownᵣ x).value.getD Fp.NaN

/-- Round down only results in negative infinity if the number is negative and too large to represent -/
theorem roundDownᵣ_infinite_iff [FloatFormat] (x : R) : (roundDownᵣ x).value = some (Fp.infinite true) ↔ (x < 0 ∧ (lowerBracket x).e > FloatFormat.max_exp) := by
  constructor
  unfold roundDownᵣ
  · intro h
    simp at h
    simp_all only [gt_iff_lt]
    apply And.intro
    · split at h
      next h_1 =>
        split at h
        next h_2 => simp_all only [Fp.infinite.injEq, Bool.true_eq]
        next h_2 => simp_all only [not_lt, reduceCtorEq]
      next h_1 => simp_all only [not_lt, reduceCtorEq]
    · split at h
      next h_1 =>
        split at h
        next h_2 => simp_all only [Fp.infinite.injEq, Bool.true_eq]
        next h_2 => simp_all only [not_lt, reduceCtorEq]
      next h_1 => simp_all only [not_lt, reduceCtorEq]
  · intro h
    simp_all only [gt_iff_lt, decide_true, ↓reduceIte, lowerBracket_neg_iff]

/-- Round down never results in positive infinity -/
theorem roundDownₓ_neq_pos_inf [FloatFormat] (x : R) : roundDownₓ x ≠ Fp.infinite false := by
  unfold roundDownₓ roundDownᵣ
  simp_all only [gt_iff_lt, lowerBracket_neg_iff, Option.getD_some, ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  split at a
  next h =>
    split at a
    next h_1 => simp_all only [Fp.infinite.injEq, Bool.true_eq_false]
    next h_1 => simp_all only [not_lt, reduceCtorEq]
  next h => simp_all only [not_lt, reduceCtorEq]

theorem roundDown_le_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundDownₓ x = 0 := by
  unfold roundDownₓ roundDownᵣ lowerBracket
  have hp := FloatFormat.valid_prec
  if h : x = 0 then
    subst h
    simp_all only [ge_iff_le, FloatFormat.valid_prec, lt_self_iff_false]
  else
    lift_lets
    have hsign := ((not_iff_not.mpr (lowerBracket_neg_iff x)).mpr hn.not_lt)
    rw [Bool.not_eq_true] at hsign

    rw [FiniteFp.smallestPosSubnormal_toVal] at hs
    extract_lets sign' e e_eff M_real m_floor is_exact midpoint guard sticky m1_final e1_final z overflow inexactResult valid_finite value
    have hsign' : sign' = false := decide_eq_false hn.not_lt
    unfold value
    if ho : z.e > FloatFormat.max_exp then
      let ho' : overflow = true := decide_eq_true ho
      exfalso
      sorry -- inconsistency
    else
      let ho' : overflow = false := decide_eq_false ho
      simp [ho, ho', hsign, hsign', z, h]
      unfold e1_final e_eff e m1_final m_floor M_real
      rw [Fp.zero_def]
      congr
      cases' max_cases (Int.log 2 |x|) (FloatFormat.min_exp) with h1 h2
      · rw [h1.left]
        sorry
      · rw [h2.left]
      unfold e_eff
      apply Nat.floor_eq_zero.mpr
      apply div_lt_one_iff.mpr
      constructor
      constructor
      · apply zpow_pos
        norm_num
      · sorry -- not too hard

theorem roundDown_zero [FloatFormat] : roundDownₓ (0 : R) = 0 := by
  unfold roundDownₓ roundDownᵣ lowerBracket
  simp_all only [↓reduceIte, QFiniteFp.zero_def, gt_iff_lt, decide_eq_true_eq, Bool.false_eq_true, Option.getD_some]
  split
  next h =>
    have := FloatFormat.exp_order
    linarith
  next h =>
    simp_all only [not_lt, FloatFormat.exp_order_le]
    rfl

-- TODO: theorem that any x : R will never round down to negative zero

theorem roundDown_le_neg_largestFiniteFloat [FloatFormat] (x : R) (hs : x < -FiniteFp.largestFiniteFloat.toVal) :
  roundDownₓ x = Fp.infinite true := by
  unfold roundDownₓ roundDownᵣ lowerBracket
  lift_lets
  extract_lets sign e e_eff M_real m_floor is_exact midpoint guard sticky m1_final e1_final z overflow inexactResult validFinite value
  simp only [Option.getD_some, value]

  unfold z

  have lfpos := FiniteFp.largestFiniteFloat_toVal_pos (R := R)
  have xpos : x < 0 := by linarith
  have xnz : x ≠ 0 := by linarith -- because simp is too dumb to infer that x < 0 implies x ≠ 0?????

  split_ifs with ho
  · rfl
  · sorry
  · sorry
  -- if ho : overflow then
  --   simp only [ho, ↓reduceIte, xnz, xpos, decide_true, sign]
  -- else
  --   exfalso
  --   unfold overflow z e1_final e_eff e at ho
  --   simp [xnz] at ho
  --   have := Int.lt_zpow_iff_log_lt (R := R) (by norm_num : 1 < 2) (r := |x|) (x := FloatFormat.max_exp) (abs_pos.mpr xnz)
  --   have ho' := this.mpr ho



  -- rw [FiniteFp.largestFiniteFloat_toVal] at hs
  -- lift_lets
  -- -- extract_lets sign e e_eff M_real m_floor is_exact midpoint guard sticky m1_final e1_final z overflow inexactResult validFinite value
  -- -- unfold value
  -- have hz : x < 0 := by
  --   apply lt_of_le_of_lt hs
  --   norm_num
  --   -- apply zpow_two_pos_of_ne_zero
  --   apply lt_mul_of_le_of_one_lt_of_pos
  --   apply zpow_nonneg (by norm_num)
  --   have := FloatFormat.valid_prec
  --   have h₀ : 1 > (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := zpow_lt_one_of_neg₀ (by norm_num) (by linarith)
  --   -- have h₁ : -1 < -(2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := by linarith
  --   -- have h₂ : 1 - 2 < -(2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := by linarith
  --   have h₃ : 1 < 2 - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1) := by linarith
  --   exact h₃
  --   apply zpow_pos (by norm_num)
  -- -- Simp is too dumb to infer that hz => x < 0
  -- have hnz : x ≠ 0 := by linarith
  -- simp only [hnz, ↓reduceIte, hz, decide_true, beq_iff_eq, ge_iff_le, Bool.if_false_left, gt_iff_lt,
  --   lt_sup_iff, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq, Option.getD_some,
  --   ite_eq_left_iff, not_or, not_lt, FloatFormat.exp_order_le, and_true, reduceCtorEq, imp_false,
  --   not_le]

  -- have := FloatFormat.valid_prec
  -- have hpos : 0 < (2 : R) ^ FloatFormat.max_exp * (2 - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1)) := by
  --   apply mul_pos
  --   apply zpow_pos (by norm_num)
  --   norm_num
  --   apply lt_trans
  --   apply zpow_lt_one_of_neg₀ (by norm_num) (by linarith)
  --   linarith
  -- have hs' : |x| ≥ (2 : R) ^ FloatFormat.max_exp * (2 - (2 : R) ^ (-(FloatFormat.prec : ℤ) + 1)) := by
  --   apply le_abs.mpr
  --   right
  --   linarith

  -- -- apply Int.lt_zpow_iff_log_lt
  -- -- have f := λ (y : ℤ) => (2:R)^y
  -- -- apply_fun (@HPow.hPow R ℤ R instHPow 2 · : ℤ → R)
  -- -- apply_fun (λ (y : ℤ) => @HPow.hPow R ℤ R instHPow 2 y)
  -- -- have hsub : (2 : R)^FloatFormat.max_exp < (2 : R)^Int.log 2 |x| := by
  -- apply ((Int.zpow_le_iff_le_log (by norm_num)) ?_).mp
  -- rw [zpow_add', zpow_one]


  -- -- have hax : |x| ≤ ((2 : R) ^ FloatFormat.max_exp * (2 - (2 :R) ^ (-(FloatFormat.prec : ℤ) + 1))) := by
  -- --   sorry
  -- -- have j := (Int.lt_zpow_iff_log_lt (R := R) (b := 2) (by norm_num) (r := |x|) (abs_pos.mpr hnz)).mp hax
  -- sorry

      -- apply zpow_lt_one₀ (by norm_num)

      -- -1 < - 2 ^ (-↑FloatFormat.prec + 1)

    -- have h := zpow_le_zpow_iff_
  -- simp [hs]


/-- Round toward positive infinity -/
def roundUp [FloatFormat] (x : R) : Fp :=
  sorry -- Implementation needed

theorem roundUp_lt_smallestPosSubnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal):
  roundUp x = 0 := by
  sorry

theorem roundUp_gt_largestFiniteFloat [FloatFormat] (x : R) (hn : 0 < x) (hs : x > FiniteFp.largestFiniteFloat.toVal):
  roundUp x = Fp.infinite false := by
  sorry

/-- Round toward zero -/
def roundTowardZero [FloatFormat] (x : R) : Fp :=
  if x ≥ 0 then roundDownₓ x else roundUp x

/-- Round to nearest, ties to even -/
def roundNearestTiesToEven [FloatFormat] (x : R) : Fp :=
  if x = 0 then 0
  else if |x| < FiniteFp.smallestPosSubnormal.toVal / 2 then 0
  else if |x| ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp then Fp.infinite (x < 0)
  else
    sorry

theorem rnEven_le_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesToEven x = 0 := by
  sorry

-- TODO: negative values?
-- TODO: better name.
-- Closely related to largest positive normal number.
theorem rnEven_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesToEven x = Fp.infinite false := by
  sorry

/-- Round to nearest, ties away from zero -/
def roundNearestTiesAwayFromZero [FloatFormat] (x : R) : Fp :=
  sorry -- Implementation needed

theorem rnAway_lt_half_subnormal [FloatFormat] (x : R) (hn : 0 < x) (hs : x < FiniteFp.smallestPosSubnormal.toVal / 2) :
  roundNearestTiesAwayFromZero x = 0 := by
  sorry

theorem rnAway_ge_inf [FloatFormat] (x : R) (hx : x ≥ (2 - 2^(1 - (FloatFormat.prec : ℤ)) / 2) * 2^FloatFormat.max_exp) :
  roundNearestTiesAwayFromZero x = Fp.infinite false := by
  sorry


inductive RoundingMode
  | Down
  | Up
  | TowardZero
  | NearestTiesToEven
  | NearestTiesAwayFromZero

def RoundingMode.toRoundingFunction [FloatFormat] (mode : RoundingMode) : R → Fp :=
  match mode with
  -- | .Down => roundDown
  | .Down => sorry
  | .Up => roundUp
  | .TowardZero => roundTowardZero
  | .NearestTiesToEven => roundNearestTiesToEven
  | .NearestTiesAwayFromZero => roundNearestTiesAwayFromZero

def RoundingMode.round [FloatFormat] (mode : RoundingMode) (x : R) : Fp :=
  mode.toRoundingFunction x

end Rounding
