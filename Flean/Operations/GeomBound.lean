import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Geometric Error Bound

The quantity `geomBound α β n = α · Σ_{k=0}^{n-1} (1+β)^k` arises naturally in
accumulator error analysis: `α` is the per-step error rate, `β` is the per-step
magnitude growth rate, and `n` is the number of steps.

## Key properties

- `geomBound_uniform`: `geomBound α α n = (1+α)^n - 1` — bridge to standard form
- `geomBound_add`: composition of two phases — the key structural lemma
- `geomBound_mul_β`: `β · geomBound α β n = α · ((1+β)^n - 1)` — division-free closed form
- `geomBound_eq_div`: `geomBound α β n = (α/β) · ((1+β)^n - 1)` when `β ≠ 0`
- `geomBound_zero_β`: `geomBound α 0 n = n · α` — no-growth case

## Design notes

Defined recursively rather than via `Finset.sum` for cleaner inductive proofs.
The `Finset.sum` equivalence is provided as `geomBound_eq_sum`.
-/

namespace GeomBound

variable {R : Type*}

/-! ## Definition -/

/-- Accumulated geometric bound: the total error from `n` steps with per-step
    error rate `α` and per-step magnitude growth rate `β`.

    `geomBound α β n = α · Σ_{k=0}^{n-1} (1+β)^k` -/
def geomBound [Mul R] [Add R] [OfNat R 1] [Pow R ℕ] [Zero R] (α β : R) : ℕ → R
  | 0 => 0
  | n + 1 => geomBound α β n + α * (1 + β) ^ n

/-! ## Structural lemmas -/

section CommRing
variable [CommRing R]

@[simp]
theorem geomBound_zero (α β : R) : geomBound α β 0 = 0 := rfl

theorem geomBound_succ (α β : R) (n : ℕ) :
    geomBound α β (n + 1) = geomBound α β n + α * (1 + β) ^ n := rfl

@[simp]
theorem geomBound_one (α β : R) : geomBound α β 1 = α := by
  simp [geomBound_succ, geomBound_zero]

theorem geomBound_two (α β : R) : geomBound α β 2 = α + α * (1 + β) := by
  simp [geomBound_succ, geomBound_zero]

/-- `geomBound` expressed as a `Finset.sum`. -/
theorem geomBound_eq_sum (α β : R) (n : ℕ) :
    geomBound α β n = α * (Finset.range n).sum (fun k => (1 + β) ^ k) := by
  induction n with
  | zero => simp [geomBound_zero]
  | succ n ih =>
    rw [geomBound_succ, ih, Finset.sum_range_succ]
    ring

/-- Power identity used in inductive proofs:
    `(1+β)^n · α + geomBound α β n = geomBound α β (n+1)` -/
theorem geomBound_step (α β : R) (n : ℕ) :
    (1 + β) ^ n * α + geomBound α β n = geomBound α β (n + 1) := by
  rw [geomBound_succ]; ring

/-- `α` factors out: `geomBound (c*α) β n = c * geomBound α β n`. -/
theorem geomBound_mul_left (c α β : R) (n : ℕ) :
    geomBound (c * α) β n = c * geomBound α β n := by
  induction n with
  | zero => simp
  | succ n ih => simp [geomBound_succ, ih]; ring

/-- Zero error rate gives zero bound. -/
@[simp]
theorem geomBound_zero_α (β : R) (n : ℕ) : geomBound 0 β n = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [geomBound_succ, ih]

/-! ## Closed forms -/

/-- Division-free closed form: `β · geomBound α β n = α · ((1+β)^n - 1)`.
    Avoids division and works in any `CommRing`. -/
theorem mul_geomBound (α β : R) (n : ℕ) :
    β * geomBound α β n = α * ((1 + β) ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geomBound_succ, mul_add, ih, pow_succ]
    ring

/-- **Uniform case**: when `α = β`, `geomBound α α n = (1+α)^n - 1`.
    This is the bridge to the current framework's `((1+α)^n - 1)` form. -/
theorem geomBound_uniform (α : R) (n : ℕ) :
    geomBound α α n = (1 + α) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [geomBound_succ, ih, pow_succ]; ring

/-- **No-growth case**: when `β = 0`, `geomBound α 0 n = n · α`. -/
theorem geomBound_zero_β (α : R) (n : ℕ) :
    geomBound α 0 n = n * α := by
  induction n with
  | zero => simp
  | succ n ih => simp [geomBound_succ, ih]; ring

/-! ## Composition -/

/-- **Composition lemma**: the total bound from `m + n` steps decomposes as
    the first `m` steps' error propagated through `n` more steps, plus the
    last `n` steps' own error.

    `geomBound α β (m+n) = geomBound α β m · (1+β)^n + geomBound α β n`

    Interpretation: Algorithm A runs m steps, then algorithm B runs n steps
    (with the same α, β). A's error `geomBound α β m` is amplified by
    `(1+β)^n` through B's magnitude growth. -/
theorem geomBound_add (α β : R) (m n : ℕ) :
    geomBound α β (m + n) = geomBound α β m * (1 + β) ^ n + geomBound α β n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega, geomBound_succ, ih, geomBound_succ]
    rw [pow_add]
    ring

end CommRing

/-! ## Monotonicity and positivity -/

section OrderedRing
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `geomBound` is nonneg when inputs are nonneg. -/
theorem geomBound_nonneg (α β : R) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    0 ≤ geomBound α β n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geomBound_succ]
    exact add_nonneg ih (mul_nonneg hα (pow_nonneg (by linarith) _))

/-- Monotone in `α`. -/
theorem geomBound_mono_α {α₁ α₂ β : R} (h : α₁ ≤ α₂) (hβ : 0 ≤ β) (n : ℕ) :
    geomBound α₁ β n ≤ geomBound α₂ β n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [geomBound_succ]
    exact add_le_add ih (mul_le_mul_of_nonneg_right h (pow_nonneg (by linarith) _))

/-- Monotone in `β` (when `α ≥ 0, β₁ ≥ 0`). -/
theorem geomBound_mono_β {α β₁ β₂ : R} (hα : 0 ≤ α) (hβ₁ : 0 ≤ β₁) (h : β₁ ≤ β₂) (n : ℕ) :
    geomBound α β₁ n ≤ geomBound α β₂ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [geomBound_succ]
    have hpow : (1 + β₁) ^ n ≤ (1 + β₂) ^ n :=
      pow_le_pow_left₀ (by linarith) (by linarith) n
    exact add_le_add ih (mul_le_mul_of_nonneg_left hpow hα)

/-- Monotone in `n` (when `α ≥ 0, β ≥ 0`). -/
theorem geomBound_mono_n {α β : R} (hα : 0 ≤ α) (hβ : 0 ≤ β) {m n : ℕ} (h : m ≤ n) :
    geomBound α β m ≤ geomBound α β n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [geomBound_add]
  linarith [le_mul_of_one_le_right (geomBound_nonneg α β hα hβ m)
              (one_le_pow₀ (show (1 : R) ≤ 1 + β by linarith) (n := k)),
            geomBound_nonneg α β hα hβ k]

/-- Strict positivity for `n ≥ 1`. -/
theorem geomBound_pos {α β : R} (hα : 0 < α) (hβ : 0 ≤ β) {n : ℕ} (hn : 0 < n) :
    0 < geomBound α β n := by
  match n, hn with
  | n + 1, _ =>
    rw [geomBound_succ]
    have := geomBound_nonneg α β hα.le hβ n
    positivity

end OrderedRing

/-! ## Interaction with `(1+β)^n` -/

section CommRing
variable [CommRing R]

/-- `1 + geomBound α α n = (1+α)^n`. Useful for magnitude recurrences. -/
theorem one_add_geomBound_uniform (α : R) (n : ℕ) :
    1 + geomBound α α n = (1 + α) ^ n := by
  rw [geomBound_uniform]; ring

/-- General version: `β · (1 + geomBound α β n) + α = β + α + β · geomBound α β n`.
    In the uniform case, `1 + geomBound = (1+α)^n`. -/
theorem geomBound_succ_eq (α β : R) (n : ℕ) :
    geomBound α β (n + 1) = α + (1 + β) * geomBound α β n := by
  induction n with
  | zero => simp [geomBound]
  | succ n ih =>
    -- geomBound (n+2) = geomBound (n+1) + α*(1+β)^{n+1}
    -- IH: geomBound (n+1) = α + (1+β) * geomBound n
    -- geomBound (n+1) = geomBound n + α*(1+β)^n
    -- Goal: geomBound n + α*(1+β)^n + α*(1+β)^{n+1} = α + (1+β)*(geomBound n + α*(1+β)^n)
    show geomBound α β (n + 1) + α * (1 + β) ^ (n + 1) =
        α + (1 + β) * (geomBound α β n + α * (1 + β) ^ n)
    rw [ih, mul_add, pow_succ]; ring

end CommRing

/-! ## Bounds relating `geomBound` to powers -/

section OrderedBounds
variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Lower bound: `geomBound α β n ≥ n · α` when `β ≥ 0`.
    Each of the n terms is at least `α · 1^k = α`. -/
theorem le_geomBound_of_nonneg (α β : R) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    (n : R) * α ≤ geomBound α β n := by
  rw [← geomBound_zero_β]
  exact geomBound_mono_β hα le_rfl hβ n

/-- Upper bound: `geomBound α β n ≤ n · α · (1+β)^n` when `α ≥ 0, β ≥ 0`.
    Each of the n terms is at most `α · (1+β)^n`. Slightly loose but clean. -/
theorem geomBound_le_mul_pow (α β : R) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    geomBound α β n ≤ (n : R) * α * (1 + β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geomBound_succ, Nat.cast_succ]
    have h1β : (1 : R) ≤ 1 + β := by linarith
    have hpow_mono : (1 + β) ^ n ≤ (1 + β) ^ (n + 1) :=
      pow_le_pow_right₀ h1β (Nat.le_succ n)
    have hn_nn : (0 : R) ≤ (n : R) := Nat.cast_nonneg n
    have hpow_nn : (0 : R) ≤ (1 + β) ^ n := pow_nonneg (by linarith) n
    have hpow_n1 : (0 : R) ≤ (1 + β) ^ (n + 1) := pow_nonneg (by linarith) (n + 1)
    -- IH: gB ≤ n*α*(1+β)^n, goal: gB + α*(1+β)^n ≤ (n+1)*α*(1+β)^{n+1}
    -- Suffices: (n+1)*α*(1+β)^n ≤ (n+1)*α*(1+β)^{n+1}
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:R) ≤ ↑n + 1) hα) hpow_nn,
               mul_le_mul_of_nonneg_left hpow_mono (mul_nonneg (by linarith : (0:R) ≤ ↑n + 1) hα)]

end OrderedBounds

/-! ## Division form -/

section FieldForm
variable [Field R]

/-- Closed form with division: `geomBound α β n = (α/β) · ((1+β)^n - 1)`.
    Requires `Field` for the division. -/
theorem geomBound_eq_div (α β : R) (hβ : β ≠ 0) (n : ℕ) :
    geomBound α β n = (α / β) * ((1 + β) ^ n - 1) := by
  have h := mul_geomBound α β n
  have : β * geomBound α β n = β * ((α / β) * ((1 + β) ^ n - 1)) := by
    rw [h]; field_simp
  exact mul_left_cancel₀ hβ this

end FieldForm

end GeomBound
