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

example : (p ∨ q) ∧ (p ∨ r) := by
  pull _ ∨ _
  guard_target =ₛ p ∨ q ∧ r
  exact test_sorry

example : (p ∨ True) ∧ (q ∨ r) := by
  push _ ∧ _
  guard_target =ₛ (p ∧ q ∨ q) ∨ p ∧ r ∨ r
  exact test_sorry

example {r : ℕ → Prop} : ∀ n : ℕ, p ∨ r n ∧ q ∧ n = 1 := by
  push ∀ n, _
  guard_target =ₛ p ∨ (∀ n, r n) ∧ q ∧ ∀ n : ℕ, n = 1
  pull ∀ n, _
  guard_target =ₛ ∀ n : ℕ, p ∨ r n ∧ q ∧ n = 1
  exact test_sorry

example {r : ℕ → Prop} : ∃ n : ℕ, p ∨ r n ∨ q ∧ n = 1 := by
  push ∃ n, _
  guard_target =ₛ p ∨ (∃ n, r n) ∨ q ∧ True
  -- the lemmas `exists_or_left`/`exist_and_left` don't exist, so they can't be tagged for `pull`
  fail_if_success pull ∃ n, _
  exact test_sorry

example : p ∨ q ∧ ∃ n : ℕ, n = 1 := by
  pull ∃ n, _
  guard_target =ₛ p ∨ ∃ n, q ∧ n = 1
  exact test_sorry

end logic
