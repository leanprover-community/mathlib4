/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Constructing (semi)normed groups from (semi)normed homs

This file defines constructions that upgrade `(Comm)Group` to `(Semi)Normed(Comm)Group`
using a `Group(Semi)normClass` when the codomain is the reals.

See `Mathlib/Analysis/Normed/Order/Hom/Ultra.lean` for further upgrades to nonarchimedean normed
groups.
-/

variable {F α : Type*} [FunLike F α ℝ]

/-- Constructs a `SeminormedGroup` structure from a `GroupSeminormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `SeminormedAddGroup` structure from an `AddGroupSeminormClass` on an
`AddGroup`. -/]
abbrev GroupSeminormClass.toSeminormedGroup [Group α] [GroupSeminormClass F α ℝ]
    (f : F) : WithSeminormedGroup α where
  norm := f
  dist x y := f (x / y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp only [← map_inv_eq_map f (x / y), inv_div]
  dist_triangle x y z := by simpa using map_mul_le_add f (x / y) (y / z)

@[to_additive]
lemma GroupSeminormClass.toSeminormedGroup_norm_eq [Group α] [GroupSeminormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedGroup f).toNorm x = f x := rfl

/-- Constructs a `NormedGroup` structure from a `GroupNormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `NormedAddGroup` structure from an `AddGroupNormClass` on an
`AddGroup`. -/]
abbrev GroupNormClass.toNormedGroup [Group α] [GroupNormClass F α ℝ]
    (f : F) : WithNormedGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := div_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive]
lemma GroupNormClass.toNormedGroup_norm_eq [Group α] [GroupNormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupNormClass.toNormedGroup f).toNorm x = f x := rfl
