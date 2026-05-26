/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Constructing (semi)normed groups from (semi)normed homs

This file defines constructions that upgrade `(Comm)Group` to `(Semi)Normed(Comm)Group`
using a `Group(Semi)normClass` when the codomain is the reals.

See `Mathlib/Analysis/Normed/Order/Hom/Ultra.lean` for further upgrades to nonarchimedean normed
groups.
-/

public section

variable {F α : Type*} [FunLike F α ℝ]

/-- missing doc -/
-- See note [reducible non-instances]
@[to_additive /-- missing doc -/]
abbrev GroupSeminormClass.toNormPseudoMetric [Group α] [GroupSeminormClass F α ℝ] (f : F) :
    NormPseudoMetric α where
  norm := f
  dist x y := f (x⁻¹ * y)
  dist_self _ := by simp
  dist_comm x y := by simp [← map_inv_eq_map f (x⁻¹ * y)]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group

/-- Constructs a `IsNormedGroup` structure from a `GroupSeminormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `IsNormedGroup` structure from an `AddGroupSeminormClass` on an
`AddGroup`. -/]
lemma GroupSeminormClass.toIsNormedGroup [Group α] [GroupSeminormClass F α ℝ] (f : F) :
    letI := toNormPseudoMetric f
    IsNormedGroup α :=
  letI := toNormPseudoMetric f
  { dist_eq _ _ := rfl }

@[to_additive]
lemma GroupSeminormClass.toNormPseudoMetric_norm_eq [Group α] [GroupSeminormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toNormPseudoMetric f).toNorm x = f x := rfl

/-- missing doc -/
-- See note [reducible non-instances]
@[to_additive /-- missing doc -/]
abbrev GroupNormClass.toNormMetric [Group α] [GroupNormClass F α ℝ] (f : F) :
    NormMetric α where
  __ := GroupSeminormClass.toNormPseudoMetric f
  eq_of_dist_eq_zero h := inv_mul_eq_one.mp (eq_one_of_map_eq_zero f h)
