/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Complex shapes with no loop

Let `c : ComplexShape ι`. We define a type class `c.HasNoLoop`
which expresses that `¬ c.Rel i i` for all `i : ι`.

-/

public section

namespace ComplexShape

variable {ι : Type*}

/-- The condition that `c.Rel i i` does not hold for any `i`. -/
class HasNoLoop (c : ComplexShape ι) : Prop where
  not_rel_self (i : ι) : ¬ c.Rel i i

section

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

lemma not_rel_self : ¬ c.Rel j j :=
  HasNoLoop.not_rel_self j

variable {j} in
lemma not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j' := by
  subst h
  exact c.not_rel_self j

instance : c.symm.HasNoLoop where
  not_rel_self j := c.not_rel_self j

@[to_dual]
lemma exists_distinct_prev_or :
    (∃ (i : ι), c.Rel j i ∧ i ≠ j) ∨ ∀ (i : ι), ¬ c.Rel j i := by
  grind +splitIndPred

@[to_dual hasNoLoop_down']
lemma hasNoLoop_up' {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (a : α) (ha : a ≠ 0) :
    (up' a).HasNoLoop where
  not_rel_self i (hi : _ = _) :=
    ha (add_left_cancel (by rw [add_zero, hi]))

@[to_dual hasNoLoop_down]
lemma hasNoLoop_up {α : Type*} [AddZeroClass α] [IsRightCancelAdd α] [IsLeftCancelAdd α]
    [One α] (ha : (1 : α) ≠ 0) :
    (up α).HasNoLoop :=
  hasNoLoop_up' _ ha

end

instance : (up ℤ).HasNoLoop := hasNoLoop_up (by simp)
instance : (up ℕ).HasNoLoop := hasNoLoop_up (by simp)
instance : (down ℤ).HasNoLoop := hasNoLoop_down (by simp)
instance : (down ℕ).HasNoLoop := hasNoLoop_down (by simp)

end ComplexShape
