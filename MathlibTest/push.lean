import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Analysis.SpecialFunctions.Log.Basic

private axiom test_sorry : ∀ {α}, α

section logic

variable {p q r : Prop}

example : False ∧ p ∨ q ∧ r := by
  push _ ∨ _
  guard_target =ₛ (q ∧ (p ∨ q)) ∧ r ∧ (p ∨ r)
  exact test_sorry

example : (p ∨ True) ∧ (q ∨ r) := by
  push _ ∧ _
  guard_target =ₛ (p ∧ q ∨ q) ∨ p ∧ r ∨ r
  exact test_sorry

example : ∀ n : ℕ, p ∨ q ∧ n = 1 := by
  push ∀ n, _
  guard_target =ₛ p ∨ q ∧ ∀ n : ℕ, n = 1
  exact test_sorry

example : ∃ n : ℕ, p ∨ q ∧ n = 1 := by
  push ∃ n, _
  guard_target =ₛ p ∨ q ∧ True
  exact test_sorry

example : (p ∨ q) ∧ (p ∨ r) := by
  pull _ ∨ _
  guard_target =ₛ p ∨ q ∧ r
  exact test_sorry

-- `exists_or` and `forall_and` cannot be used by `pull` when `∃`/`∀` is only on one side
example : p ∧ (q ∨ ∀ n : ℕ, n = 1) := by
  pull ∀ n, _
  guard_target =ₛ p ∧ ∀ n, q ∨ n = 1
  exact test_sorry

example : p ∨ q ∧ ∃ n : ℕ, n = 1 := by
  pull ∃ n, _
  guard_target =ₛ p ∨ ∃ n, q ∧ n = 1
  exact test_sorry

end logic
