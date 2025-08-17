import Mathlib.Tactic.Push

private axiom test_sorry : ∀ {α}, α

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
  guard_target =ₐ p ∨ q ∧ ∀ n : ℕ, n = 1
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
  guard_target =ₐ p ∧ ∀ n, q ∨ n = 1
  exact test_sorry

example : p ∨ q ∧ ∃ n : ℕ, n = 1 := by
  pull ∃ n, ·
  guard_target =ₐ p ∨ ∃ n, q ∧ n = 1
  exact test_sorry

-- the following examples still need more tagging to work

-- example (a b c : Real) (ha : 0 < a) (hc : 0 < c) :
--     Real.log (a ^ 4 * (1/c) / a * Real.exp b) =
--       4 * Real.log a + (0 - Real.log c) - Real.log a + b := by
--   push (disch := positivity) Real.log
--   rfl

-- example (a b : ℚ) : ((a + b⁻¹ + 1) / 2) ^ 2 = 0 := by
--   push · ^ ·
--   guard_target = (a ^ 2 + 2 * a * b⁻¹ + (b ^ 2)⁻¹ + 2 * (a + b⁻¹) * 1 + 1) / 2 ^ 2 = 0
--   ring_nf
--   exact test_sorry


-- example (a b c : α) (s : Set α) : a ∈ (∅ ∪ (Set.univ ∩ (({b, c} \ sᶜᶜ) ∪ {b | b = a}))) := by
--   push · ∈ ·
--   guard_target =ₛ False ∨ True ∧ ((a = b ∨ a = c) ∧ ¬¬a ∉ s ∨ a = a)
--   exact test_sorry

-- example (s t : Set α) : s ∈ 𝒫 t := by
--   push · ∈ ·
--   guard_target =ₛ s ⊆ t
--   exact test_sorry

-- example (s t : Set α) (a : α) : (s ∪ t ∩ {a} ∩ {x | x ≠ a} ∩ {_x | True})ᶜ = s := by
--   push ·ᶜ
--   guard_target =ₛ sᶜ ∩ (tᶜ ∪ {x | x ≠ a} ∪ {a} ∪ {a | ¬True}) = s
--   exact test_sorry
