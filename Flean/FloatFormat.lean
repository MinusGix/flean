import Mathlib.Data.Int.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Flean.Linearize.Linearize
import Lean.Elab.Tactic.Location

@[ext]
structure Radix where
  val : ℤ
  valid : val ≥ 2
deriving Repr, DecidableEq
namespace Radix

instance : LawfulBEq Radix where
  eq_of_beq {a b} h := by
    rw [beq_iff_eq] at h
    exact h
  rfl {a} := by simp only [beq_self_eq_true]

-- TODO: linear order on Radix

def Binary : Radix := ⟨2, by norm_num⟩
def Decimal : Radix := ⟨10, by norm_num⟩

variable {β : Radix}

@[simp]
theorem gt_zero : β.val > 0 := by
  have h := β.valid
  omega

@[simp]
theorem gt_one : β.val > 1 := by
  have h := β.valid
  omega

@[simp]
theorem zero_lt : 0 < β.val := by
  have h := β.valid
  omega

@[simp]
theorem one_lt : 1 < β.val := by
  have h := β.valid
  omega

@[simp]
theorem ne_zero : β.val ≠ 0 := by
  have h := β.valid
  omega

@[simp]
theorem two_le : 2 ≤ β.val := by
  have h := β.valid
  omega

end Radix

class FloatFormat where
  -- radix : Radix
  prec : ℕ
  min_exp : ℤ
  max_exp : ℤ
  valid_prec : prec ≥ 2
  exp_order : min_exp < max_exp
  max_exp_pos : 0 < max_exp
  min_exp_nonpos : min_exp ≤ 0

attribute [simp] FloatFormat.valid_prec
attribute [simp] FloatFormat.exp_order
attribute [simp] FloatFormat.max_exp_pos
attribute [simp] FloatFormat.min_exp_nonpos

namespace FloatFormat

def isStandardExpRange [FloatFormat] : Prop :=
  FloatFormat.min_exp = 1 - FloatFormat.max_exp

end FloatFormat

-- TODO(minor): Should we split the emax pow requirement the is standard exp range?
class StdFloatFormat extends FloatFormat where
  -- emax is of the form 2^n - 1
  exp_pow : ℕ
  -- We could make this > 1 without really losing anything
  exp_pow_pos : exp_pow > 0
  max_exp_pow : max_exp = 2 ^ exp_pow - 1
  st : FloatFormat.isStandardExpRange

attribute [simp] StdFloatFormat.exp_pow_pos
attribute [simp] StdFloatFormat.max_exp_pow
attribute [simp] StdFloatFormat.st

namespace FloatFormat

def radix [FloatFormat] : Radix := Radix.Binary

theorem radix_val_eq_two [FloatFormat] : FloatFormat.radix.val = 2 := rfl

-- TODO: does e4m3 not have infinities?
-- See: https://arxiv.org/pdf/2209.05433
-- But we don't currently support that.
-- TODO: Support floating point numbers that don't have infinities
-- I fear that there's no consistent general way to do this. That it might be better to treat them as a separate wrapper type that considers the infinities as non-actual values.

-- def E4M3Binary8 : StdFloatFormat := {
--   prec := 4,
--   min_exp := -6,
--   max_exp := 7,
--   valid_prec := by norm_num,
--   exp_order := by norm_num,
--   max_exp_pos := by norm_num,
--   min_exp_nonpos := by norm_num,

--   exp_pow := 3
--   exp_pow_pos := by norm_num
--   max_exp_pow := by norm_num
--   st := by
--     unfold isStandardExpRange
--     norm_num
-- }

-- def E5M2Binary8 : StdFloatFormat := {
--   prec := 3,
--   min_exp := -14,
--   max_exp := 15,
--   valid_prec := by norm_num,
--   exp_order := by norm_num,
--   max_exp_pos := by norm_num,
--   min_exp_nonpos := by norm_num,

--   exp_pow := 4
--   exp_pow_pos := by norm_num
--   max_exp_pow := by norm_num
--   st := by
--     unfold isStandardExpRange
--     norm_num
-- }

def Binary16 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 11,
  min_exp := -14,
  max_exp := 15,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 4
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- Commonly known as 'float' or 'single-precision' -/
def Binary32 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 24,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- Commonly known as 'double' or 'double-precision' -/
def Binary64 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 53,
  min_exp := -1022,
  max_exp := 1023,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 10
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

def Binary128 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 113,
  min_exp := -16382,
  max_exp := 16383,
  valid_prec := by norm_num,
  exp_order := by norm_num
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 14
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

-- TODO: 80-bit floating point formats

/-- BFloat16 format. Has a lower precision but a higher exponent, which gives it a higher range for less precision. -/
def BF16 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 8,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

/-- NVIDIA's Tensor Float 32 Format. This uses the same half-precision of FP16, while having the exponent of FP32.
This is termed '32' though it really only uses 19 bits, but in practice it is stored using 32-bits.  -/
def TF32 : StdFloatFormat := {
  -- radix := Radix.Binary,
  prec := 11,
  min_exp := -126,
  max_exp := 127,
  valid_prec := by norm_num,
  exp_order := by norm_num,
  max_exp_pos := by norm_num,
  min_exp_nonpos := by norm_num,

  exp_pow := 7
  exp_pow_pos := by norm_num
  max_exp_pow := by norm_num
  st := by
    unfold isStandardExpRange
    norm_num
}

-- TODO: is there a way to just put @ simp on fields?

-- Unfortunately simp doesn't seem to understand it can turn < into ≤?? so I have to have this def
@[simp]
theorem exp_order_le [FloatFormat] : min_exp ≤ max_exp := FloatFormat.exp_order.le

@[simp]
theorem prec_pow_le [FloatFormat] {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] : (4 : R) ≤ (2 : R)^FloatFormat.prec := by
  rw [show (4 : R) = (2 : R)^(2 : ℕ) by norm_num]
  apply pow_le_pow_right₀ (by norm_num) FloatFormat.valid_prec

theorem prec_pred_pow_le [FloatFormat] {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] : (2 : R) ≤ (2 : R)^(FloatFormat.prec - 1) := by
  conv_lhs => rw [show (2 : R) = (2 : R)^(1 : ℕ) by norm_num]
  have := FloatFormat.valid_prec
  gcongr
  norm_num
  omega

@[simp]
theorem pow_prec_pred_lt [FloatFormat] : 2^(FloatFormat.prec - 1) < 2^FloatFormat.prec := by
  have := FloatFormat.valid_prec
  apply pow_lt_pow_right₀ (by norm_num) (by omega)

theorem pow_prec_pred_lt' [FloatFormat] {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] : (2 : R)^(FloatFormat.prec - 1) < (2 : R)^FloatFormat.prec := by
  have := FloatFormat.valid_prec
  apply pow_lt_pow_right₀ (by norm_num) (by omega)

theorem zpow_prec_pred_lt' [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] : (2 : R)^((FloatFormat.prec : ℤ) - 1) < (2 : R)^(FloatFormat.prec) := by
  have := FloatFormat.valid_prec
  rw [zpow_sub_one₀ (by norm_num)]
  norm_num

theorem zpow_neg_prec_plus_one_le_two [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  : (2 : R)^(-(FloatFormat.prec : ℤ) + 1) ≤ (2 : R) := by
  conv_rhs => rw [← zpow_one (2 : R)]
  gcongr
  <;> norm_num

/-- 2^(prec - 1) where the power is nat is equivalent to 2^(prec - 1) as integers
This is somehow annoying to work with otherwise, Lean's existing casting facilities are too simplistic.
This being simp makes it somehow used by norm_num? -/
@[simp]
theorem pow_prec_sub_one_nat_int [FloatFormat] {R : Type*} [Field R]
  : (2 : R)^(FloatFormat.prec - 1) = (2 : R)^((FloatFormat.prec : ℤ) - 1) := by
  conv => rhs; rw [← Nat.cast_one]
  rw [← Nat.cast_sub]
  rw [zpow_natCast]
  have := FloatFormat.valid_prec
  omega


theorem zpow_min_exp_prec_plus_one_le_zpow_min_exp_sub_one
  {R : Type*}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloatFormat] : (2 : R)^(FloatFormat.min_exp - FloatFormat.prec + 1) ≤ (2 : R)^(FloatFormat.min_exp - 1) := by
  gcongr
  norm_num
  have := FloatFormat.valid_prec
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]
  apply add_le_add_left
  norm_num

theorem zpow_min_exp_prec_plus_one_le_zpow_min_exp
  {R : Type*}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloatFormat] : (2 : R)^(FloatFormat.min_exp - FloatFormat.prec + 1) ≤ (2 : R)^(FloatFormat.min_exp) := by
  have := zpow_min_exp_prec_plus_one_le_zpow_min_exp_sub_one (R := R)
  apply le_trans this
  simp only [Nat.one_lt_ofNat, zpow_le_zpow_iff_right₀, tsub_le_iff_right, le_add_iff_nonneg_right,
    zero_le_one]

-- @[simp high]
theorem pow_prec_nat_int [FloatFormat] {R : Type*} [Field R]
  : (2 : R)^(FloatFormat.prec) = (2 : R)^((FloatFormat.prec : ℤ)) := by
  rw [zpow_natCast]

theorem natCast_pow_prec [FloatFormat] {R : Type*} [Field R]
  : (2 : R)^FloatFormat.prec = ↑((2 : ℕ) ^ FloatFormat.prec) := by norm_cast

theorem natCast_pow_prec_pred [FloatFormat] {R : Type*} [Field R]
  : (2 : R)^FloatFormat.prec - (1 : R) = ↑((2 : ℕ)^FloatFormat.prec - (1 : ℕ)) := by
  rw [Nat.cast_sub]
  norm_cast
  apply one_le_pow₀ (by norm_num)

theorem natCast_pow_prec_msb [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  : (2 : R)^(FloatFormat.prec - 1) = ↑((2 : ℕ)^FloatFormat.prec) * 2⁻¹ := by
  -- zify
  rw [← zpow_natCast, Int.natCast_sub, Int.natCast_one]
  rw [zpow_natCast_sub_one₀]
  rw [div_eq_mul_inv]
  norm_num
  norm_num
  have := FloatFormat.valid_prec
  omega

theorem natCast_pow_prec_msb' [FloatFormat] {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  : (2 : R)^(FloatFormat.prec - 1) = ↑((2 : ℕ)^(FloatFormat.prec - 1)) := by
  simp only [pow_prec_sub_one_nat_int, Nat.cast_pow, Nat.cast_ofNat]

namespace Const

theorem const_pow_le_pow_prec [FloatFormat] : 2^2 ≤ 2^FloatFormat.prec := by
  gcongr
  norm_num
  exact FloatFormat.valid_prec

theorem const_le_pow_prec [FloatFormat] : 4 ≤ 2^FloatFormat.prec := by
  simp only [prec_pow_le]

end Const

-- def Decimal32 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 7,
--   min_exp := -95,
--   max_exp := 96,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

-- def Decimal64 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 16,
--   min_exp := -383,
--   max_exp := 384,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

-- def Decimal128 : FloatFormat := {
--   radix := Radix.Decimal,
--   prec := 34,
--   min_exp := -6143,
--   max_exp := 6144,
--   valid_prec := by norm_num,
--   valid_exp := by norm_num
-- }

theorem standardExpRange_pos [FloatFormat] (standard : FloatFormat.isStandardExpRange) : 0 < FloatFormat.max_exp - FloatFormat.min_exp := by
  have := FloatFormat.exp_order
  rw [standard] at this ⊢
  omega

-- theorem binary16_standard_exp_range : Binary16.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary16, min_exp, max_exp]
--   norm_num

-- theorem binary32_standard_exp_range : Binary32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary32, min_exp, max_exp]
--   norm_num

-- theorem binary64_standard_exp_range : Binary64.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary64, min_exp, max_exp]
--   norm_num

-- theorem binary128_standard_exp_range : Binary128.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Binary128, min_exp, max_exp]
--   norm_num

-- theorem bf16_standard_exp_range : BF16.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [BF16, min_exp, max_exp]
--   norm_num

-- theorem tf32_standard_exp_range : TF32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [TF32, min_exp, max_exp]
--   norm_num

-- theorem decimal32_standard_exp_range : Decimal32.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal32, min_exp, max_exp]
--   norm_num

-- theorem decimal64_standard_exp_range : Decimal64.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal64, min_exp, max_exp]
--   norm_num

-- theorem decimal128_standard_exp_range : Decimal128.isStandardExpRange := by
--   unfold isStandardExpRange
--   simp only [Decimal128, min_exp, max_exp]
--   norm_num

end FloatFormat

namespace StdFloatFormat

@[simp]
def max_exp_def [StdFloatFormat] : FloatFormat.max_exp = 2 ^ StdFloatFormat.exp_pow - 1 := StdFloatFormat.max_exp_pow

@[simp]
def std_exp_range_def [StdFloatFormat] : FloatFormat.min_exp = 1 - FloatFormat.max_exp := StdFloatFormat.st

end StdFloatFormat

-- open Lean Elab Meta Tactic Parser.Tactic in
-- /-- `flinearize!` is a specialized version of `linearize!` that includes common FloatFormat lemmas.
-- It is equivalent to `linearize! [FloatFormat.valid_prec, FloatFormat.exp_order,
-- FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos]` -/
-- syntax (name := flinearizeBang) "flinearize!" (&" only")? (" [" term,* "]")? (location)? : tactic

-- open Lean Elab Meta Tactic Parser.Tactic in
-- elab_rules : tactic
--   | `(tactic| flinearize! $[only%$o]? $[ [ $args,* ] ]? $[$loc:location]?) => do
--     -- Call linearize! with the default FloatFormat lemmas plus any additional arguments
--     match o, args with
--     | some _, some args =>
--       evalTactic (← `(tactic| linearize! only [FloatFormat.valid_prec, FloatFormat.exp_order, FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos, FloatFormat.prec_pred_pow_le, $args,*] $[$loc:location]?))
--     | some _, none =>
--       evalTactic (← `(tactic| linearize! only [FloatFormat.valid_prec, FloatFormat.exp_order, FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos, FloatFormat.prec_pred_pow_le] $[$loc:location]?))
--     | none, some args =>
--       evalTactic (← `(tactic| linearize! [FloatFormat.valid_prec, FloatFormat.exp_order, FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos, FloatFormat.prec_pred_pow_le, $args,*] $[$loc:location]?))
--     | none, none =>
--       evalTactic (← `(tactic| linearize! [FloatFormat.valid_prec, FloatFormat.exp_order, FloatFormat.max_exp_pos, FloatFormat.min_exp_nonpos, FloatFormat.prec_pred_pow_le] $[$loc:location]?))

open Lean Elab Meta Tactic Parser.Tactic in
syntax (name := flinearizeBang) "flinearize!" (" (" term ")")? (&" only")? (" [" term,* "]")? (location)? : tactic

open Lean Elab Meta Tactic Parser.Tactic in
elab_rules : tactic
  | `(tactic| flinearize! $[($R_user)]? $[only%$o]? $[ [ $args,* ] ]? $[$loc:location]?) => do
    -- Determine the type `R` to use for specialization.
    let R_opt : Option (TSyntax `term) ←
      match R_user with
      | some r =>
        -- 1. If the user provides `(R)`, use that. It has the highest priority.
        pure (some r)
      | none =>
        -- 2. If no type is given, try to infer it from the main goal.
        let goalExpr ← getMainTarget
        trace[linarith] "goalExpr: {goalExpr}"
        let mut inferredType : Option Expr := none
        -- Look for binary relations like `a < b` or `a ≤ b`
        if goalExpr.isAppOfArity ``LT.lt 4 || goalExpr.isAppOfArity ``LE.le 4 then
          let lhs := goalExpr.getAppArgs[0]!
          trace[linarith] "lhs: {lhs}"
          inferredType := some lhs
        -- Look for equality `a = b` (which is `Eq R a b`)
        else if goalExpr.isAppOfArity ``Eq 3 then
          trace[linarith] "goalExpr: {goalExpr}"
          inferredType := some (goalExpr.getAppArgs[0]!)
        trace[linarith] "inferredType: {inferredType}"

        match inferredType with
        | some typeExpr =>
          -- Convert the inferred type `Expr` back into a `Syntax` object.
          -- pure (some (← delab typeExpr))
          let typeSyntax ← typeExpr.toSyntax
          trace[linarith] "typeSyntax: {typeSyntax}"
          pure (some typeSyntax)
        | none =>
          -- 3. If inference fails, proceed without a type.
          pure none

    -- Build the list of lemmas for linarith.
    let mut allTerms : Array (TSyntax `term) :=
      #[← `(FloatFormat.valid_prec), ← `(FloatFormat.exp_order),
        ← `(FloatFormat.max_exp_pos), ← `(FloatFormat.min_exp_nonpos), ← `(FloatFormat.pow_prec_pred_lt)]

    -- Add generic lemmas, specializing them if we have a type for R.
    match R_opt with
    | some r =>
      trace[linarith] "r: {r}"
      allTerms := allTerms.push (← `(FloatFormat.prec_pred_pow_le (R := $r)))
    | none =>
      allTerms := allTerms.push (← `(FloatFormat.prec_pred_pow_le))

    -- Append any additional lemmas provided by the user.
    if let some userArgs := args then
      allTerms := allTerms ++ userArgs.getElems

    -- Construct and evaluate the final tactic call.
    let tac ← `(tactic| linearize! [$allTerms,*])
    evalTactic tac


open Lean Elab Meta Tactic Parser.Tactic in
syntax (name := flinarith) "flinarith" (" (" term ")")? (" [" term,* "]")? : tactic

open Lean Elab Meta Tactic Parser.Tactic in
elab_rules : tactic
  | `(tactic| flinarith $[($R_user)]? $[ [ $args,* ] ]?) => do
    -- Determine the type `R` to use for specialization.
    let R_opt : Option (TSyntax `term) ←
      match R_user with
      | some r =>
        -- 1. If the user provides `(R)`, use that. It has the highest priority.
        pure (some r)
      | none =>
        -- 2. If no type is given, try to infer it from the main goal.
        let goalExpr ← getMainTarget
        trace[linarith] "goalExpr: {goalExpr}"
        let mut inferredType : Option Expr := none
        -- Look for binary relations like `a < b` or `a ≤ b`
        if goalExpr.isAppOfArity ``LT.lt 4 || goalExpr.isAppOfArity ``LE.le 4 then
          let lhs := goalExpr.getAppArgs[0]!
          trace[linarith] "lhs: {lhs}"
          inferredType := some lhs
        -- Look for equality `a = b` (which is `Eq R a b`)
        else if goalExpr.isAppOfArity ``Eq 3 then
          trace[linarith] "goalExpr: {goalExpr}"
          inferredType := some (goalExpr.getAppArgs[0]!)
        trace[linarith] "inferredType: {inferredType}"

        match inferredType with
        | some typeExpr =>
          -- Convert the inferred type `Expr` back into a `Syntax` object.
          -- pure (some (← delab typeExpr))
          let typeSyntax ← typeExpr.toSyntax
          trace[linarith] "typeSyntax: {typeSyntax}"
          pure (some typeSyntax)
        | none =>
          -- 3. If inference fails, proceed without a type.
          pure none

    -- Build the list of lemmas for linarith.
    let mut allTerms : Array (TSyntax `term) :=
      #[← `(FloatFormat.valid_prec), ← `(FloatFormat.exp_order),
        ← `(FloatFormat.max_exp_pos), ← `(FloatFormat.min_exp_nonpos), ← `(FloatFormat.pow_prec_pred_lt)]

    -- Add generic lemmas, specializing them if we have a type for R.
    match R_opt with
    | some r =>
      trace[linarith] "r: {r}"
      allTerms := allTerms.push (← `(FloatFormat.prec_pred_pow_le (R := $r)))
    | none =>
      allTerms := allTerms.push (← `(FloatFormat.prec_pred_pow_le))

    -- Append any additional lemmas provided by the user.
    if let some userArgs := args then
      allTerms := allTerms ++ userArgs.getElems

    -- Construct and evaluate the final tactic call.
    let tac ← `(tactic| linarith [$allTerms,*])
    evalTactic tac


open Lean Elab Meta Tactic Parser.Tactic in
-- Define the syntax for the `fomega` tactic.
-- It accepts an optional list of user-provided terms.
syntax (name := fomega) "fomega" (" [" term,* "]")? : tactic

-- Define the elaborator for the tactic.
open Lean Elab Meta Tactic Parser.Tactic in
elab_rules : tactic
  | `(tactic| fomega $[ [ $args,* ] ]?) => do
    -- `withMainContext` ensures that context changes are properly managed.
    withMainContext do
      -- 1. Define the default `FloatFormat` lemmas.
      --    Lemmas that are generic over a ring `R` are specialized to `ℕ`,
      --    since `omega` operates on natural numbers.
      let defaultLemmas : Array (TSyntax `term) := #[
        ← `(FloatFormat.valid_prec),
        ← `(FloatFormat.exp_order),
        ← `(FloatFormat.max_exp_pos),
        ← `(FloatFormat.min_exp_nonpos),
        ← `(FloatFormat.prec_pred_pow_le (R := ℕ)),
        ← `(FloatFormat.pow_prec_pred_lt)
      ]

      -- 2. Combine the default lemmas with any lemmas provided by the user.
      let allLemmas :=
        if let some userArgs := args then
          defaultLemmas ++ userArgs.getElems
        else
          defaultLemmas

      -- 3. Introduce every lemma from the combined list into the local context.
      --    The `have` tactic adds each one as a new hypothesis.
      for l in allLemmas do
        evalTactic (← `(tactic| have := $l))

      -- 4. Finally, call `omega`, which can now use the newly introduced facts.
      evalTactic (← `(tactic| omega))
