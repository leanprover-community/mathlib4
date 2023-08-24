import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.GeneralizeProofs
import Std.Tactic.GuardExpr
import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
def List.nthLe (l : List α) (n) (h : n < l.length) : α := sorry

example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1 2].nth_le 1 _ = 2
  generalize_proofs h
  -- h : 1 < [1 2].length
  -- ⊢ [1 2].nth_le 1 h = 2
  sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 := by
  generalize_proofs a
  guard_hyp a : ∃ x, x < 2
  guard_target = Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) = Classical.choose (⟨x, h⟩ : ∃ x, x < 2) := by
  generalize_proofs a
  guard_hyp a : ∃ x, x < 2
  guard_target = Classical.choose a = Classical.choose a
  rfl

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) =
  Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs a
  guard_hyp a : ∃ x, x < 2
  guard_target = Classical.choose a = Classical.choose _
  sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) =
  Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs
  guard_target = Classical.choose _ = Classical.choose _
  sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) =
  Classical.choose (⟨x, Nat.lt_succ_of_lt h⟩ : ∃ x, x < 3) := by
  generalize_proofs _ a
  guard_hyp a : ∃ x, x < 3
  guard_target = Classical.choose _ = Classical.choose a
  sorry

example (a : ∃ x, x < 2) : Classical.choose a < 2 := by
  generalize_proofs
  guard_target = Classical.choose a < 2
  exact Classical.choose_spec a

example (a : ∃ x, x < 2) : Classical.choose a < 2 := by
  generalize_proofs t
  guard_target = Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) (H : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2) :
    Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 := by
  generalize_proofs a at H ⊢
  guard_hyp a : ∃ x, x < 2
  guard_hyp H : Classical.choose a < 2
  guard_target = Classical.choose a < 2
  exact H

-- FIXME: result is not type correct
-- example (H : ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y) :
--   ∀ y, ∃ (x : ℕ) (h : x < y), Classical.choose (⟨x, h⟩ : ∃ x, x < y) < y := by
--   generalize_proofs a at H ⊢

attribute [local instance] Classical.propDecidable

example (H : ∀ x, x = 1) : (if h : ∃ (k : ℕ), k = 1 then Classical.choose h else 0) = 1 := by
  rw [dif_pos]
  rotate_left
  { exact ⟨1, rfl⟩ }
  generalize_proofs h g
  guard_target = Classical.choose h = 1
  apply H
