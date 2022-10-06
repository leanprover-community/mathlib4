import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.GeneralizeProofs
import Std.Tactic.GuardExpr

def List.nthLe (l : List α) (n) (h : n < l.length) : α := sorry

example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1 2].nth_le 1 _ = 2
  generalize_proofs h
  -- h : 1 < [1 2].length
  -- ⊢ [1 2].nth_le 1 h = 2
  sorry

example (x : ℕ) (h : x < 2) : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 :=
by
  generalize_proofs a
  guard_hyp a : ∃ x, x < 2
  guard_target == Classical.choose a < 2
  exact Classical.choose_spec a

example (a : ∃ x, x < 2) : Classical.choose a < 2 :=
by
  generalize_proofs
  guard_target == Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) (a : ∃ x, x < 2) : Classical.choose a < 2 :=
by
  generalize_proofs
  guard_target == Classical.choose a < 2
  exact Classical.choose_spec a

example (x : ℕ) (h : x < 2) (H : Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2) :
  Classical.choose (⟨x, h⟩ : ∃ x, x < 2) < 2 :=
by
  generalize_proofs a at H ⊢
  guard_hyp a : ∃ x, x < 2
  guard_hyp H : Classical.choose a < 2
  guard_target == Classical.choose a < 2
  exact H

attribute [local instance] Classical.propDecidable

example (H : ∀ x, x = 1) : (if h : ∃ (k : ℕ), k = 1 then Classical.choose h else 0) = 1 :=
by
  rw [dif_pos]
  rotate_left
  { exact ⟨1, rfl⟩ }
  generalize_proofs h g
  guard_target == Classical.choose h = 1
  apply H
