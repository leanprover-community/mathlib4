import Mathlib.Tactic.Relation.Trans
import Std.Data.Nat.Lemmas

-- testing that the attribute is recognized and used
def nleq (a b : Nat) : Prop := a ≤ b

@[trans] def nleq_trans : nleq a b → nleq b c → nleq a c := Nat.le_trans

example (a b c : Nat) : nleq a b → nleq b c → nleq a c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example (a b c : Nat) : nleq a b → nleq b c → nleq a c := by intros; trans <;> assumption

-- using `Trans` typeclass
@[trans] def eq_trans {a b c : α} : a = b → b = c → a = c := by
  intro h₁ h₂
  apply Eq.trans h₁ h₂

example (a b c : Nat) : a = b → b = c → a = c := by intros; trans <;> assumption

example (a b c : Nat) : a = b → b = c → a = c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example : @Trans Nat Nat Nat (. ≤ .) (. ≤ .) (. ≤ .) := inferInstance

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intros h₁ h₂
  trans ?b
  case b => exact b
  exact h₁
  exact h₂

example (a b c : α) (R : α → α → Prop) [Trans R R R] : R a b → R b c → R a c := by
  intros h₁ h₂
  trans ?b
  case b => exact b
  exact h₁
  exact h₂

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intros h₁ h₂
  trans
  exact h₁
  exact h₂

example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by intros; trans <;> assumption

example (a b c : Nat) : a < b → b < c → a < c := by
  intro h₁ h₂
  trans b
  assumption
  assumption

example (a b c : Nat) : a < b → b < c → a < c := by intros; trans <;> assumption

example (x n p : Nat) (h₁ : n * Nat.succ p ≤ x) : n * p ≤ x := by
  trans
  · apply Nat.mul_le_mul_left; apply Nat.le_succ
  · apply h₁
