import Mathlib.Tactic.ExtractGoal
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Order.Basic
import Mathlib.Order.Nat

set_option pp.unicode.fun true
set_option autoImplicit true
set_option linter.unusedVariables false

-- the example in the documentation for the tactic.
/-- info: theorem extracted_1 (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := sorry -/
#guard_msgs (info) in
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal
  exact h₀.trans h₁

/-- info: theorem extracted_1 (i j k : ℕ) (h₁ : j ≤ k) : i ≤ k := sorry -/
#guard_msgs (info) in
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal h₁
  exact h₀.trans h₁

-- an example with all binder types
/-- info: theorem extracted_1.{v, u} {α : Type u} {β : Type v} [h : Sub β] (f : α → β) (a : α) {b : β} :
  f a - b = f a - b := sorry
-/
#guard_msgs in
example {α : Type u} {β : Type v} [Add α] [h : Sub β] (f : α → β) ⦃_g : ℤ⦄ (a : α) {b : β} :
    f a - b = f a - b := by
  extract_goal
  rfl

-- an example with a hygienic variable
/-- info: theorem extracted_1 (n : ℕ) : n + 1 = n + 1 := sorry -/
#guard_msgs in
example (n : ℕ) : n = n := by
  cases n
  rfl
  extract_goal
  rfl

-- an example with auto-implicit `Sort` and variable
/--
info: theorem extracted_1.{u_1} {α : Sort u_1} {n : α} : n = n := sorry
-/
#guard_msgs in
example : n = n := by
  extract_goal
  rfl

/--
info: theorem extracted_1 {z : Int} :
  @Exists.{1} Nat fun (n : Nat) ↦ @Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt n) z := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {z : Int} : ∃ n : Nat, ↑n = z := by
  set_option pp.all true in
  extract_goal
  sorry

/--
info: theorem foo : True := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (n : ℕ) : True := by
  extract_goal using foo
  sorry

/--
info: theorem foo (n : ℕ) : True := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (n : ℕ) : True := by
  extract_goal n using foo
  sorry

/-- error: unknown identifier 'k' -/
#guard_msgs in
example (n : ℕ) : True := by
  extract_goal k

/--
info: theorem extracted_1 (n : ℕ) : True := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (n : ℕ) : True := by
  extract_goal *
  sorry

-- Clears `i` since neither `n` nor the goal depends on it.
/--
info: theorem extracted_1 (n : ℕ) : True := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (n : ℕ) (i : Fin n) : True := by
  extract_goal n
  sorry

/--
info: theorem extracted_1 (n : ℕ) (i : Fin n) : True := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (n : ℕ) (i : Fin n) : True := by
  extract_goal i
  sorry

-- Contradiction proof gives full context:
/--
info: theorem extracted_1 (h : 1 = 2) : False := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (h : 1 = 2) : False := by
  extract_goal
  sorry

-- Check mdata is cleared:
/--
info: theorem extracted_1 (h : 1 = 2) : False := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : False := by
  have h : 1 = 2 := sorry
  extract_goal
  sorry

-- Check that fvar elaboration is with respect to the main local context
/--
info: theorem extracted_1 (h : 1 = 2) : False := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1 = 2 → False := by
  intro h
  extract_goal h
  sorry

-- Check that sets local context correctly
/--
info: theorem extracted_1 (m : ℕ) : m < m + 1 := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ n, n < n + 1 := by
  intro m
  extract_goal
  sorry

-- Throwing metavariables into the terms
/--
info: theorem extracted_1 (m : ℕ) (this : m < m.succ.succ) : m < m + 1 := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : ∀ n, n < n + 1 := by
  intro m
  show _
  have : m < _ := Nat.lt.step (Nat.lt.base m)
  extract_goal
  sorry
