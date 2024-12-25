/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Group.Int

/-!
# Complex shapes with no loop

Let `c : ComplexShape ι`. We define a type class `c.HasNoLoop`
which expresses that `¬ c.Rel i i` for all `i : ι`.

-/

namespace ComplexShape

variable {ι : Type*}

/-- The condition that `c.Rel i i` does not hold for any `i`. -/
class HasNoLoop (c : ComplexShape ι) : Prop where
  not_rel_self (i : ι) : ¬ c.Rel i i

section

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

lemma not_rel_self : ¬ c.Rel j j :=
  HasNoLoop.not_rel_self j

instance : c.symm.HasNoLoop where
  not_rel_self j := c.not_rel_self j

lemma exists_distinct_prev_or :
    (∃ (k : ι), c.Rel j k ∧ j ≠ k) ∨ ∀ (k : ι), ¬ c.Rel j k := by
  by_cases h : ∃ (k : ι), c.Rel j k
  · obtain ⟨k, hk⟩ := h
    refine Or.inl ⟨k, hk, ?_⟩
    rintro rfl
    exact c.not_rel_self j hk
  · exact Or.inr (by simpa using h)

lemma exists_distinct_next_or :
    (∃ (i : ι), c.Rel i j ∧ i ≠ j) ∨ ∀ (i : ι), ¬ c.Rel i j := by
  by_cases h : ∃ (i : ι), c.Rel i j
  · obtain ⟨i, hi⟩ := h
    refine Or.inl ⟨i, hi, ?_⟩
    rintro rfl
    exact c.not_rel_self i hi
  · exact Or.inr (by simpa using h)

lemma up'_hasNoLoop {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (up' a).HasNoLoop where
  not_rel_self i (hi : _ = _) :=
    ha (add_left_cancel (by rw [add_zero, hi]))

lemma down'_hasNoLoop {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (down' a).HasNoLoop := by
  have := up'_hasNoLoop a ha
  exact inferInstanceAs (up' a).symm.HasNoLoop

lemma up_hasNoLoop {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (up α).HasNoLoop :=
  up'_hasNoLoop _ ha

lemma down_hasNoLoop {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (down α).HasNoLoop :=
  down'_hasNoLoop _ ha

end

instance : (up ℤ).HasNoLoop := up_hasNoLoop (by simp)
instance : (up ℕ).HasNoLoop := up_hasNoLoop (by simp)
instance : (down ℤ).HasNoLoop := down_hasNoLoop (by simp)
instance : (down ℕ).HasNoLoop := down_hasNoLoop (by simp)

end ComplexShape
