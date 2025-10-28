/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Order.Hom.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Constructing nonarchimedean (ultrametric) normed groups from nonarchimedean normed homs

This file defines constructions that upgrade `Add(Comm)Group` to `(Semi)NormedAdd(Comm)Group`
using an `AddGroup(Semi)normClass` when the codomain is the reals and the hom is nonarchimedean.

## Implementation details

The lemmas need to assume `[Dist α]` to be able to be stated, so they take an extra argument
that shows that this distance instance is propositionally equal to the one that comes from the
hom-based `AddGroupSeminormClass.toSeminormedAddGroup f` construction. To help at use site,
the argument is an autoparam that resolves by definitional equality when using these constructions.
-/

variable {F α : Type*} [FunLike F α ℝ]

/-- Proves that when a `SeminormedAddGroup` structure is constructed from an
`AddGroupSeminormClass` that satisfies `IsNonarchimedean`, the group has an `IsUltrametricDist`. -/
lemma AddGroupSeminormClass.isUltrametricDist [AddGroup α] [AddGroupSeminormClass F α ℝ]
    [inst : Dist α] {f : F} (hna : IsNonarchimedean f)
    (hd : inst = (AddGroupSeminormClass.toSeminormedAddGroup f).toDist := by rfl) :
    IsUltrametricDist α :=
  ⟨fun x y z ↦ by simpa only [hd, dist_eq_norm, AddGroupSeminormClass.toSeminormedAddGroup_norm_eq,
      ← sub_add_sub_cancel x y z] using hna _ _⟩
