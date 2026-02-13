import Flean.Operations.Sub
import Flean.Operations.Mul
import Flean.Operations.Div

/-! # Floating-Point Operator Instances

These instances expose the class-driven operation APIs (`fpAdd`, `fpSub`,
`fpMul`, `fpDiv`) through standard operators on `Fp`.

Use by providing a contextual rounding execution policy:
`[FloatFormat] [RModeExec]`.
-/

section Instances

variable [FloatFormat] [RModeExec]

instance : HAdd Fp Fp Fp where
  hAdd := fpAdd

instance : HSub Fp Fp Fp where
  hSub := fpSub

instance : HMul Fp Fp Fp where
  hMul := fpMul

instance : HDiv Fp Fp Fp where
  hDiv := fpDiv

@[simp] theorem add_eq_fpAdd (x y : Fp) : x + y = fpAdd x y := rfl
@[simp] theorem sub_eq_fpSub (x y : Fp) : x - y = fpSub x y := rfl
@[simp] theorem mul_eq_fpMul (x y : Fp) : x * y = fpMul x y := rfl
@[simp] theorem div_eq_fpDiv (x y : Fp) : x / y = fpDiv x y := rfl

end Instances
