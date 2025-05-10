import Mathlib.Tactic.RenameBVar
import Lean

set_option linter.unusedVariables false
axiom test_sorry {α : Sort _} : α

/- This test is somewhat flaky since it depends on the pretty printer. -/
/--
trace: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (n : ℕ), ∃ m, P n m
⊢ ∀ (l : ℕ), ∃ m, P l m
---
trace: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (q : ℕ), ∃ m, P q m
⊢ ∀ (l : ℕ), ∃ m, P l m
---
trace: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (q : ℕ), ∃ m, P q m
⊢ ∀ (l : ℕ), ∃ n, P l n
---
trace: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (q : ℕ), ∃ m, P q m
⊢ ∀ (m : ℕ), ∃ n, P m n
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m := by
  trace_state
  rename_bvar n → q at h
  trace_state
  rename_bvar m → n
  trace_state
  rename_bvar l → m
  trace_state
  exact h

/--
trace: case intro
a b c : Int
h2 : b ∣ c
k : Int
hk : b = a * k
⊢ ∃ k, c = a * k
---
trace: case intro
a b c : Int
h2 : b ∣ c
k : Int
hk : b = a * k
⊢ ∃ m, c = a * m
-/
#guard_msgs in
example (a b c : Int) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  rcases h1 with ⟨k, hk⟩
  show ∃ k, c = a * k
  trace_state
  rename_bvar k → m
  trace_state
  exact test_sorry
