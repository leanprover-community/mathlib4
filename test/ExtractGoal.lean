import Mathlib.Tactic.ExtractGoal
import Mathlib.Data.Nat.Basic

set_option pp.unicode.fun true

-- the example in the documentation for the tactic.
/-- info: theorem extracted_1 (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := sorry -/
#guard_msgs (info) in
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extract_goal
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
/--
info: theorem extracted_1 (n : ℕ) : Nat.succ n = Nat.succ n := sorry
-/
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
