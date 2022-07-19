import Mathlib.Tactic.Trans
import Mathlib.Init.Data.Nat.Lemmas
open Nat

-- testing that the attribute is recognized and used
def nleq : Nat → Nat → Prop
| a, b => a ≤ b

@[trans] def nleqTrans {a b c : Nat} : nleq a b → nleq b c → nleq a c := Nat.le_trans

example (a b c : Nat): nleq a b → nleq b c → nleq a c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): nleq a b → nleq b c → nleq a c :=
   by intros ; trans ; repeat (assumption)

-- using `Trans` typeclass
@[trans] def eqTrans {α : Type}{a b c : α}:  a = b → b = c → a = c := by
    intro h₁ h₂
    apply Eq.trans h₁ h₂


example (a b c : Nat): a = b → b = c → a = c :=
   by intros ; trans ; repeat (assumption)

example (a b c : Nat): a = b → b = c → a = c := by
    intro h₁ h₂
    trans b
    assumption
    assumption

example : Trans ((. ≤ . : Nat → Nat → Prop))
        (. ≤ . : Nat → Nat → Prop) (. ≤ . : Nat → Nat → Prop) := inferInstance

example (a b c : Nat): a ≤ b → b ≤ c → a ≤ c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): a ≤ b → b ≤ c → a ≤ c :=
   by intros ; trans ; repeat (assumption)


example (a b c : Nat): a < b → b < c → a < c := by
   intro h₁ h₂
   trans b
   assumption
   assumption

example (a b c : Nat): a < b → b < c → a < c :=
   by intros ; trans ; repeat (assumption)


example (x n p : ℕ) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  cases eq_zero_or_pos n with
  | inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n*p ≤ x := by
        trans
        · apply Nat.mul_le_mul_left; apply le_succ
        · apply h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        apply h₁
      rw [sub_succ, ← IH h₂]
      rw [div_eq_sub_div h₀ h₃]
      simp [add_one, Nat.pred_succ, mul_succ, Nat.sub_sub]
