import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Analysis.SpecialFunctions.Log.Basic

private axiom test_sorry : ∀ {α}, α

section logic

variable {p q r : Prop}

example : False ∧ p ∨ q ∧ r := by
  push · ∨ ·
  guard_target =ₛ (q ∧ (p ∨ q)) ∧ r ∧ (p ∨ r)
  exact test_sorry

example : (p ∨ True) ∧ (q ∨ r) := by
  push · ∧ ·
  guard_target =ₛ (p ∧ q ∨ q) ∨ p ∧ r ∨ r
  exact test_sorry

example : ∀ n : ℕ, p ∨ q ∧ n = 1 := by
  push ∀ n, ·
  guard_target =ₛ p ∨ q ∧ ∀ n : ℕ, n = 1
  exact test_sorry

example : ∃ n : ℕ, p ∨ q ∧ n = 1 := by
  push ∃ n, ·
  guard_target =ₛ p ∨ q ∧ True
  exact test_sorry

example : (p ∨ q) ∧ (p ∨ r) := by
  pull · ∨ ·
  guard_target =ₛ p ∨ q ∧ r
  exact test_sorry

-- `exists_or` and `forall_and` cannot be used by `pull` when `∃`/`∀` is only on one side
example : p ∧ (q ∨ ∀ n : ℕ, n = 1) := by
  pull ∀ n, ·
  guard_target =ₛ p ∧ ∀ n, q ∨ n = 1
  exact test_sorry

example : p ∨ q ∧ ∃ n : ℕ, n = 1 := by
  pull ∃ n, ·
  guard_target =ₛ p ∨ ∃ n, q ∧ n = 1
  exact test_sorry

end logic

section lambda

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  push fun x ↦ ·
  with_reducible rfl

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  simp only [pushFun]

end lambda

section membership

example (x : Nat) (A : Set Nat) : x ∈ ∅ ∪ Set.univ ∩ ({a | a = 4} \ Aᶜ) := by
  push · ∈ ·
  guard_target =ₛ (False ∨ True ∧ x = 4 ∧ ¬x ∉ A)
  exact test_sorry

example (A : Set Nat) : A ∈ 𝒫 A := by
  push · ∈ ·
  rfl

example (x y : Nat) (A B : Set Nat) : (x, y) ∈ A ×ˢ B := by
  push · ∈ ·
  -- Note: we don't allow `push` to unfold projections, which is a bit unfortunate in this case
  guard_target =ₛ (x, y).1 ∈ A ∧ (x, y).2 ∈ B
  pull · ∈ ·
  guard_target =ₛ (x, y) ∈ A ×ˢ B
  exact test_sorry

example (x y : Nat) (A : Set Nat) : (x, y) ∈ Set.diagonal Nat ∪ Set.offDiag A := by
  push · ∈ ·
  guard_target =ₛ (x, y).1 = (x, y).2 ∨ (x, y).1 ∈ A ∧ (x, y).2 ∈ A ∧ (x, y).1 ≠ (x, y).2
  exact test_sorry

example (x y z : Nat) : x ∈ ({x, y, z, y, x} : Set Nat) := by
  push · ∈ ·
  guard_target =ₛ x = x ∨ x = y ∨ x = z ∨ x = y ∨ x = x
  exact test_sorry

example (x : Nat) (A B C : Set Nat) : x ∈ A ∧ ¬ x ∈ B ∨ x ∈ C := by
  pull · ∈ ·
  guard_target =ₛ x ∈ A ∩ Bᶜ ∪ C
  exact test_sorry

example (a b c : α) (s : Set α) : a ∈ (∅ ∪ (Set.univ ∩ (({b, c} \ sᶜᶜ) ∪ {b | b = a}))) := by
  push · ∈ ·
  guard_target =ₛ False ∨ True ∧ ((a = b ∨ a = c) ∧ ¬¬a ∉ s ∨ a = a)
  exact test_sorry

end membership

section log

example (a b : ℝ) (ha : a > 0) (hb : b > 0) : Real.log (a * b) = Real.log a + Real.log b := by
  set_option trace.Meta.Tactic.simp true in
  pull (disch := positivity) Real.log

example (a b c : Real) (ha : 0 < a) (hc : 0 < c) :
    Real.log (a ^ 4 * c⁻¹ / a * Real.exp b) = 4 * Real.log a + -Real.log c - Real.log a + b := by
  push (disch := positivity) Real.log
  pull (disch := positivity) Real.log
  guard_target = Real.log (a ^ 4 * c⁻¹ / a) + b = 4 * Real.log a + Real.log c⁻¹ - Real.log a + b
  push (disch := positivity) Real.log
  rfl

end log

-- the following examples still need more tagging to work

-- example (a b : ℚ) : ((a + b⁻¹ + 1) / 2) ^ 2 = 0 := by
--   push · ^ ·
--   guard_target =ₛ (a ^ 2 + 2 * a * b⁻¹ + (b ^ 2)⁻¹ + 2 * (a + b⁻¹) * 1 + 1) / 2 ^ 2 = 0
--   ring_nf
--   exact test_sorry

-- example (s t : Set α) (a : α) : (s ∪ t ∩ {a} ∩ {x | x ≠ a} ∩ {_x | True})ᶜ = s := by
--   push ·ᶜ
--   guard_target =ₛ sᶜ ∩ (tᶜ ∪ {x | x ≠ a} ∪ {a} ∪ {a | ¬True}) = s
--   exact test_sorry
