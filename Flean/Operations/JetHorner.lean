import Flean.Operations.AffineFold

/-!
# Jet Horner: Simultaneous Value and Derivative Evaluation

Evaluates a polynomial `p(x)` and its derivative `p'(x)` simultaneously
using a coupled 2D recurrence:

```
(v₀, d₀) = (aₙ, 0)
(vₖ, dₖ) = (x·vₖ₋₁ + aₙ₋ₖ, x·dₖ₋₁ + vₖ₋₁)
```

After `n` steps: `vₙ = p(x)` and `dₙ = p'(x)`.

The state `(v, d)` is a "1-jet" — the polynomial value plus its first derivative.
Each step is an affine map on `R × R`, making this a natural AffineFold instance:
`L(v, d) = (x·v, x·d + v)` with offset `(c, 0)`.

## Key Property

`L` is additive (it's linear), so `jetHornerExact_affine` follows from AffineFold.
The propagation `jetHornerProp` captures how perturbations in the initial jet propagate
through the coupled recurrence — perturbation in `v₀` affects both `v` and `d`.
-/

namespace JetHorner

open AffineFold

variable {R : Type*} [Field R]

/-! ## Exact Evaluation -/

/-- Exact jet Horner evaluation: simultaneously computes value and derivative. -/
def jetHornerExact : List R → R → R → R → R × R
  | [], v, d, _ => (v, d)
  | c :: cs, v, d, x => jetHornerExact cs (x * v + c) (x * d + v) x

/-- Jet Horner's linear map: `L(v, d) = (x·v, x·d + v)`. -/
def jetHornerL (x : R) : R × R → R × R := fun (v, d) => (x * v, x * d + v)

theorem jetHornerL_additive (x : R) :
    ∀ a b, jetHornerL x (a + b) = jetHornerL x a + jetHornerL x b :=
  fun (v₁, d₁) (v₂, d₂) => by
    simp [jetHornerL, Prod.ext_iff]; constructor <;> ring

/-- Jet Horner offsets: coefficient contributes to value, zero to derivative. -/
def jetHornerOffsets (cs : List R) : List (R × R) := cs.map (·, 0)

/-- `affineFold` with `jetHornerL` and `jetHornerOffsets` equals `jetHornerExact`. -/
theorem affineFold_eq_jetHornerExact (cs : List R) (v d x : R) :
    affineFold (jetHornerL x) (jetHornerOffsets cs) (v, d) =
      jetHornerExact cs v d x := by
  induction cs generalizing v d with
  | nil => simp [affineFold, jetHornerOffsets, jetHornerExact]
  | cons c cs ih =>
    simp only [affineFold, jetHornerOffsets, jetHornerExact, jetHornerL, List.map_cons]
    show affineFold _ _ (x * v + c, x * d + v + 0) = _
    rw [add_zero]
    exact ih _ _

/-- **Jet Horner affine property** (from generic AffineFold).

    Perturbing `(v, d)` by `(ev, ed)` shifts the final state by
    `affineProp (jetHornerL x) n (ev, ed)`. -/
theorem jetHornerExact_affine (cs : List R) (v d ev ed x : R) :
    jetHornerExact cs (v + ev) (d + ed) x =
      ((jetHornerExact cs v d x).1 +
        (affineProp (jetHornerL x) cs.length (ev, ed)).1,
       (jetHornerExact cs v d x).2 +
        (affineProp (jetHornerL x) cs.length (ev, ed)).2) := by
  have h := affineFold_affine (jetHornerL x) (jetHornerL_additive x)
    (jetHornerOffsets cs) (v, d) (ev, ed)
  rw [affineFold_eq_jetHornerExact, affineFold_eq_jetHornerExact] at h
  have hlen : (jetHornerOffsets cs).length = cs.length := by simp [jetHornerOffsets]
  rw [hlen] at h
  simp only [Prod.add_def] at h
  have h1 := congr_arg Prod.fst h
  have h2 := congr_arg Prod.snd h
  simp only [] at h1 h2
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h1, h2⟩

/-! ## Exact Decomposition -/

/-- **Exact decomposition for jet Horner**: computed + error propagation = exact.

    This is the 2D AffineFold exact decomposition specialized to jet evaluation.
    Both the value error AND the derivative error are captured. -/
theorem jetHorner_exact_decomposition
    (cs errors : List (R × R)) (v d : R) (computed_v computed_d : R) (x : R)
    (hlen : cs.length = errors.length)
    (hcomputed : (computed_v, computed_d) =
      affineFold (jetHornerL x) (List.zipWith (· - ·) cs errors) (v, d)) :
    (computed_v, computed_d) + affineFold (jetHornerL x) errors (0, 0) =
      affineFold (jetHornerL x) cs (v, d) :=
  affineFold_exact_decomposition (jetHornerL x) (jetHornerL_additive x)
    cs errors (v, d) (computed_v, computed_d) hlen hcomputed

end JetHorner
