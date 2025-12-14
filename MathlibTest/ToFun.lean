import Mathlib.Tactic.ToFun
import Mathlib.Analysis.Normed.Ring.Basic

@[to_fun]
theorem Function.mul_comm (f g : ℝ → ℝ) : f * g = g * f := _root_.mul_comm f g

/-- info: Function.fun_mul_comm (f g : ℝ → ℝ) : (fun i => f i * g i) = fun i => g i * f i -/
#guard_msgs in
#check Function.fun_mul_comm


-- Test that it also works when the generated proof is not a `rfl` proof:

@[to_additive (attr := push ← high)]
lemma Pi.mul_def' {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] (f g : ∀ i, M i) :
    f * g = fun i ↦ f i * g i := (rfl)

@[to_fun]
theorem Function.mul_comm' (f g : ℝ → ℝ) : f * g = g * f := _root_.mul_comm f g

/-- info: Function.fun_mul_comm' (f g : ℝ → ℝ) : (fun i => f i * g i) = fun i => g i * f i -/
#guard_msgs in
#check Function.fun_mul_comm'
