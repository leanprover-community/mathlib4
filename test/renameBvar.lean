import Mathlib.Tactic.RenameBVar

/- This test is somewhat flaky since it depends on the pretty printer. -/
/--
info: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (n : ℕ), ∃ m, P n m
⊢ ∀ (l : ℕ), ∃ m, P l m
---
info: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (q : ℕ), ∃ m, P q m
⊢ ∀ (l : ℕ), ∃ m, P l m
---
info: ℕ : Sort u_1
P : ℕ → ℕ → Prop
h : ∀ (q : ℕ), ∃ m, P q m
⊢ ∀ (l : ℕ), ∃ n, P l n
---
info: ℕ : Sort u_1
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
warning: renaming the variable `n to itself has no effect
---
warning: renaming the variable `n to itself has no effect
-/
#guard_msgs in
example {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ m, P n m) : ∀ n, ∀ m, P n m := by
  rename_bvar n → n
  rename_bvar n → n at h
  exact h

-- Renaming a non-existent variable does not warn, at the moment.
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n, P n) : ∀ m, P m := by
  rename_bvar Q → R
  exact h
