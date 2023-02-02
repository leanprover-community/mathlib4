/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes

! This file was ported from Lean 3 source module group_theory.presented_group
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.FreeGroup
import Mathbin.GroupTheory.QuotientGroup

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `presented_group rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `to_group f`: the canonical group homomorphism `presented_group rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/


variable {α : Type _}

/-- Given a set of relations, rels, over a type `α`, presented_group constructs the group with
generators `x : α` and relations `rels` as a quotient of free_group `α`.-/
def PresentedGroup (rels : Set (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels
#align presented_group PresentedGroup

namespace PresentedGroup

instance (rels : Set (FreeGroup α)) : Group (PresentedGroup rels) :=
  QuotientGroup.Quotient.group _

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `free_group α`. -/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  QuotientGroup.mk (FreeGroup.of x)
#align presented_group.of PresentedGroup.of

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `presented_group rels` to `G`.
-/
variable {G : Type _} [Group G] {f : α → G} {rels : Set (FreeGroup α)}

-- mathport name: exprF
local notation "F" => FreeGroup.lift f

variable (h : ∀ r ∈ rels, F r = 1)

theorem closure_rels_subset_ker : Subgroup.normalClosure rels ≤ MonoidHom.ker F :=
  Subgroup.normalClosure_le_normal fun x w => (MonoidHom.mem_ker _).2 (h x w)
#align presented_group.closure_rels_subset_ker PresentedGroup.closure_rels_subset_ker

theorem to_group_eq_one_of_mem_closure : ∀ x ∈ Subgroup.normalClosure rels, F x = 1 := fun x w =>
  (MonoidHom.mem_ker _).1 <| closure_rels_subset_ker h w
#align presented_group.to_group_eq_one_of_mem_closure PresentedGroup.to_group_eq_one_of_mem_closure

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `presented_group rels → G`. -/
def toGroup : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)
#align presented_group.to_group PresentedGroup.toGroup

@[simp]
theorem toGroup.of {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift.of
#align presented_group.to_group.of PresentedGroup.toGroup.of

theorem toGroup.unique (g : PresentedGroup rels →* G) (hg : ∀ x : α, g (of x) = f x) :
    ∀ {x}, g x = toGroup h x := fun x =>
  QuotientGroup.induction_on x fun _ => FreeGroup.lift.unique (g.comp (QuotientGroup.mk' _)) hg
#align presented_group.to_group.unique PresentedGroup.toGroup.unique

end ToGroup

instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

end PresentedGroup

