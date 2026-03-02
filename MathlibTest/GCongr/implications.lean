import Mathlib.Tactic.GCongr

variable {a b c d : Prop}

example (h : a → b) : (a ∧ ¬b) ∨ c → (b ∧ ¬a) ∨ c := by gcongr
example (h : a → b) : (a ∧ ¬b) ∨ c → (b ∧ ¬a) ∨ c := by gcongr ?_ ∧ ¬?_ ∨ c

example (h : d → b) : (a ∨ b ∧ c → d) → (a ∨ d ∧ c → b) := by gcongr
example (h : d → b) : (a ∨ b ∧ c → d) → (a ∨ d ∧ c → b) := by gcongr a ∨ ?_ ∧ c → ?_

example (h : a → b) : ¬ ¬ ¬ b → ¬ ¬ ¬ a := by gcongr
example (h : a → b) : ¬ ¬ ¬ b → ¬ ¬ ¬ a := by gcongr ¬ ¬ ¬ ?_

example (h : a → b) : (∃ i, ∀ j, i ∧ b → j) → (∃ i, ∀ j, i ∧ a → j) := by gcongr
example (h : a → b) : (∃ i, ∀ j, i ∧ b → j) → (∃ i, ∀ j, i ∧ a → j) := by
  gcongr ∃ i, ∀ j, i ∧ ?_ → j

example (h : c → b) : (a → b → c) → (a → b → b) := by
  gcongr 1
  guard_target =ₛ (b → c) → (b → b)
  gcongr 1

/-- error: gcongr did not make progress -/
#guard_msgs in
example (h : ∀ n : Nat, 0 ≤ n) : ∀ n : Int, 0 ≤ n := by
  revert h
  gcongr
