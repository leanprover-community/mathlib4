import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Analysis.SpecialFunctions.Log.Basic

private axiom test_sorry : ∀ {α}, α

section logic

variable {p q r : Prop}

/-- info: (q ∧ (p ∨ q)) ∧ r ∧ (p ∨ r) -/
#guard_msgs in
#push Or False ∧ p ∨ q ∧ r

/-- info: (p ∨ q) ∧ (p ∨ r) -/
#guard_msgs in
#push Or (p ∨ q) ∧ (p ∨ r)

/-- info: (p ∧ q ∨ q) ∨ p ∧ r ∨ r -/
#guard_msgs in
#push And (p ∨ True) ∧ (q ∨ r)

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

/-- info: p ∨ ∃ x, q ∧ x = 1 -/
#guard_msgs in
#pull Exists p ∨ q ∧ ∃ n : ℕ, n = 1

/--
info: DiscrTree branch for Or:
  (node
   (* => (node
     (False => (node #[or_false:1000]))
     (And => (node (* => (node (* => (node #[or_and_left:1000]))))))
     (True => (node #[or_true:1000]))))
   (False => (node (* => (node #[false_or:1000]))))
   (And => (node (* => (node (* => (node (* => (node #[and_or_right:1000]))))))))
   (True => (node (* => (node #[true_or:1000])))))
-/
#guard_msgs in
#push_discr_tree Or

end logic

section lambda

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  push fun x ↦ _
  with_reducible rfl

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  simp only [pushFun]

end lambda

section membership

example (x : Nat) (A : Set Nat) : x ∈ ∅ ∪ Set.univ ∩ ({a | a = 4} \ Aᶜ) := by
  push _ ∈ _
  guard_target =ₛ (False ∨ True ∧ x = 4 ∧ ¬x ∉ A)
  exact test_sorry

example (A : Set Nat) : A ∈ 𝒫 A := by
  push _ ∈ _
  rfl

example (x y : Nat) (A B : Set Nat) : (x, y) ∈ A ×ˢ B := by
  push _ ∈ _
  -- `push _ ∈ _` can unpack the pair `(x, y)` because a specialized lemma has been tagged
  guard_target =ₛ x ∈ A ∧ y ∈ B
  exact test_sorry

example (p : Nat × Nat) (A B : Set Nat) : p ∈ A ×ˢ B := by
  push _ ∈ _
  guard_target =ₛ p.1 ∈ A ∧ p.2 ∈ B
  pull _ ∈ _
  guard_target =ₛ p ∈ A ×ˢ B
  exact test_sorry

example (p : Nat × Nat) (A : Set Nat) : p ∈ Set.diagonal Nat ∪ Set.offDiag A := by
  push _ ∈ _
  guard_target =ₛ p.1 = p.2 ∨ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2
  exact test_sorry

example (x y z : Nat) : x ∈ ({x, y, z, y, x} : Set Nat) := by
  push _ ∈ _
  guard_target =ₛ x = x ∨ x = y ∨ x = z ∨ x = y ∨ x = x
  exact test_sorry

example (x : Nat) (A B C : Set Nat) : x ∈ A ∧ ¬ x ∈ B ∨ x ∈ C := by
  pull _ ∈ _
  guard_target =ₛ x ∈ A ∩ Bᶜ ∪ C
  exact test_sorry

example (a b c : α) (s : Set α) : a ∈ (∅ ∪ (Set.univ ∩ (({b, c} \ sᶜᶜ) ∪ {b | b = a}))) := by
  push _ ∈ _
  guard_target =ₛ False ∨ True ∧ ((a = b ∨ a = c) ∧ ¬¬a ∉ s ∨ a = a)
  exact test_sorry

end membership

section log

example (a b : ℝ) (ha : a > 0) (hb : b > 0) : Real.log (a * b) = Real.log a + Real.log b := by
  pull (disch := positivity) Real.log
  rfl

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
--   push _ ^ _
--   guard_target =ₛ (a ^ 2 + 2 * a * b⁻¹ + (b ^ 2)⁻¹ + 2 * (a + b⁻¹) * 1 + 1) / 2 ^ 2 = 0
--   ring_nf
--   exact test_sorry

-- example (s t : Set α) (a : α) : (s ∪ t ∩ {a} ∩ {x | x ≠ a} ∩ {_x | True})ᶜ = s := by
--   push _ᶜ
--   guard_target =ₛ sᶜ ∩ (tᶜ ∪ {x | x ≠ a} ∪ {a} ∪ {a | ¬True}) = s
--   exact test_sorry
