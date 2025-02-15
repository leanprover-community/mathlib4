import Mathlib.Analysis.SpecialFunctions.Log.Basic

private axiom test_sorry : ∀ {α}, α

set_option autoImplicit true
-- set_option trace.Meta.Tactic.simp true


example (a b c : Real) (ha : 0 < a) (hc : 0 < c) :
    Real.log (a ^ 4 * (1/c) / a * Real.exp b) =
      4 * Real.log a + (0 - Real.log c) - Real.log a + b := by
  push (disch := positivity) Real.log
  rfl

example (a b : ℚ): ((a + b⁻¹ + 1) / 2) ^ 2 = 0 := by
  push HPow.hPow
  guard_target =ₛ (a ^ 2 + 2 * a * b⁻¹ + b⁻¹ ^ 2 + 2 * (a + b⁻¹) * 1 + 1) / 2 ^ 2 = 0
  ring_nf
  exact test_sorry


example : False ∧ q ∨ r ∧ s := by
  push Or
  guard_target =ₛ (r ∧ (q ∨ r)) ∧ s ∧ (q ∨ s)
  exact test_sorry

example : (p ∨ True) ∧ (r ∨ s) := by
  push And
  guard_target =ₛ (p ∧ r ∨ r) ∨ p ∧ s ∨ s
  exact test_sorry

example : ∀ n : ℕ, p ∧ q ∨ n = 1 := by
  push Forall
  guard_target =ₐ p ∧ q ∨ ∀ n : ℕ, n = 1
  exact test_sorry

example : ∃ n : ℕ, p ∧ q ∨ n = 1 := by
  push Exists
  guard_target =ₛ p ∧ q ∨ True
  exact test_sorry

example (a b c : α) (s : Set α): a ∈ (∅ ∪ (Set.univ ∩ (({b, c} \ sᶜᶜ) ∪ {b | b = a}))) := by
  push Membership.mem
  guard_target =ₛ False ∨ True ∧ ((a = b ∨ a = c) ∧ ¬¬a ∉ s ∨ a = a)
  exact test_sorry

example (s t : Set α) : s ∈ 𝒫 t := by
  push Membership.mem
  guard_target =ₛ s ⊆ t
  exact test_sorry

example (s t : Set α) (a : α) : (s ∪ t ∩ {a} ∩ {x | x ≠ a} ∩ {_x | True})ᶜ = s := by
  push compl
  guard_target =ₛ sᶜ ∩ (tᶜ ∪ {x | x ≠ a} ∪ {a} ∪ {a | ¬True}) = s
  exact test_sorry
-- powerset

-- complement
-- complement singleton
