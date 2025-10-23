import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Analysis.SpecialFunctions.Pow.Real

private axiom test_sorry : ∀ {α}, α

section logic

variable {p q r : Prop}

/-- info: (q ∧ (p ∨ q)) ∧ r ∧ (p ∨ r) -/
#guard_msgs in
#push Or => False ∧ p ∨ q ∧ r

/-- info: (p ∨ q) ∧ (p ∨ r) -/
#guard_msgs in
#push Or => (p ∨ q) ∧ (p ∨ r)

/-- info: (p ∧ q ∨ q) ∨ p ∧ r ∨ r -/
#guard_msgs in
#push And => (p ∨ True) ∧ (q ∨ r)

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
#pull Exists => p ∨ q ∧ ∃ n : ℕ, n = 1

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

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  pull fun _ ↦ _
  with_reducible rfl

example : (fun x : ℕ ↦ x ^ 2 + 1 * 0 - 5 • 6) = id ^ 2 + 1 * 0 - 5 • 6 := by
  simp only [pullFun]

end lambda

section log

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.log (a * b) = Real.log a + Real.log b := by
  pull (disch := positivity) Real.log
  rfl

variable (a b c : Real) (ha : 0 < a) (hc : 0 < c)

/-- info: ↑4 * Real.log a + -Real.log c - b * Real.log a + b -/
#guard_msgs in
#push (disch := positivity) Real.log => Real.log (a ^ 4 * c⁻¹ / a ^ b * Real.exp b)

/-- info: Real.log (a ^ 4 * c⁻¹ / a ^ b) + b -/
#guard_msgs in
#pull (disch := positivity) Real.log => 4 * Real.log a + -Real.log c - b * Real.log a + b


end log
