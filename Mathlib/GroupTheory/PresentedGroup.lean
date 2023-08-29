/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes
-/
import Mathlib.GroupTheory.FreeGroup
import Mathlib.GroupTheory.QuotientGroup

#align_import group_theory.presented_group from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedGroup rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `toGroup f`: the canonical group homomorphism `PresentedGroup rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/


variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedGroup` constructs the group with
generators `x : α` and relations `rels` as a quotient of `FreeGroup α`. -/
def PresentedGroup (rels : Set (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels
#align presented_group PresentedGroup

namespace PresentedGroup

instance (rels : Set (FreeGroup α)) : Group (PresentedGroup rels) :=
  QuotientGroup.Quotient.group _

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `FreeGroup α`. -/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  QuotientGroup.mk (FreeGroup.of x)
#align presented_group.of PresentedGroup.of

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `PresentedGroup rels` to `G`.
-/
variable {G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}

-- mathport name: exprF
local notation "F" => FreeGroup.lift f

-- Porting note: `F` has been expanded, because `F r = 1` produces a sorry.
variable (h : ∀ r ∈ rels, FreeGroup.lift f r = 1)

theorem closure_rels_subset_ker : Subgroup.normalClosure rels ≤ MonoidHom.ker F :=
  Subgroup.normalClosure_le_normal fun x w ↦ (MonoidHom.mem_ker _).2 (h x w)
#align presented_group.closure_rels_subset_ker PresentedGroup.closure_rels_subset_ker

theorem to_group_eq_one_of_mem_closure : ∀ x ∈ Subgroup.normalClosure rels, F x = 1 :=
  fun _ w ↦ (MonoidHom.mem_ker _).1 <| closure_rels_subset_ker h w
#align presented_group.to_group_eq_one_of_mem_closure PresentedGroup.to_group_eq_one_of_mem_closure

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `PresentedGroup rels → G`. -/
def toGroup : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)
#align presented_group.to_group PresentedGroup.toGroup

@[simp]
theorem toGroup.of {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift.of
#align presented_group.to_group.of PresentedGroup.toGroup.of

theorem toGroup.unique (g : PresentedGroup rels →* G)
    (hg : ∀ x : α, g (PresentedGroup.of x) = f x) : ∀ {x}, g x = toGroup h x := by
  intro x
  -- ⊢ ↑g x = ↑(toGroup h) x
  refine' QuotientGroup.induction_on x _
  -- ⊢ ∀ (z : FreeGroup α), ↑g ↑z = ↑(toGroup h) ↑z
  exact fun _ ↦ FreeGroup.lift.unique (g.comp (QuotientGroup.mk' _)) hg
  -- 🎉 no goals
#align presented_group.to_group.unique PresentedGroup.toGroup.unique

end ToGroup

instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

end PresentedGroup
