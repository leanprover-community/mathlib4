/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Newell Jensen
-/
import Mathlib.GroupTheory.FreeGroup.Basic
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

/-- The generators of a presented group generate the presented group. That is, the subgroup closure
of the set of generators equals `⊤`. -/
@[simp]
theorem closure_range_of (rels : Set (FreeGroup α)) :
    Subgroup.closure (Set.range (PresentedGroup.of : α → PresentedGroup rels)) = ⊤ := by
  have : (PresentedGroup.of : α → PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this, Set.range_comp, ← MonoidHom.map_closure (QuotientGroup.mk' _),
    FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_top_of_surjective _ (QuotientGroup.mk'_surjective _)

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `PresentedGroup rels` to `G`.
-/
variable {G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}

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
  refine QuotientGroup.induction_on x ?_
  exact fun _ ↦ FreeGroup.lift.unique (g.comp (QuotientGroup.mk' _)) hg
#align presented_group.to_group.unique PresentedGroup.toGroup.unique

@[ext]
theorem ext {φ ψ : PresentedGroup rels →* G} (hx : ∀ (x : α), φ (.of x) = ψ (.of x)) : φ = ψ := by
  unfold PresentedGroup
  ext
  apply hx

variable {β : Type*}

/-- Presented groups of isomorphic types are isomorphic. -/
def equivPresentedGroup (rels : Set (FreeGroup α)) (e : α ≃ β) :
    PresentedGroup rels ≃* PresentedGroup (FreeGroup.freeGroupCongr e '' rels) :=
  QuotientGroup.congr (Subgroup.normalClosure rels)
    (Subgroup.normalClosure ((FreeGroup.freeGroupCongr e) '' rels)) (FreeGroup.freeGroupCongr e)
    (Subgroup.map_normalClosure rels (FreeGroup.freeGroupCongr e).toMonoidHom
      (FreeGroup.freeGroupCongr e).surjective)

theorem equivPresentedGroup_apply_of (x : α) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    equivPresentedGroup rels e (PresentedGroup.of x) =
      PresentedGroup.of (rels := FreeGroup.freeGroupCongr e '' rels) (e x) := rfl

theorem equivPresentedGroup_symm_apply_of (x : β) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    (equivPresentedGroup rels e).symm (PresentedGroup.of x) =
      PresentedGroup.of (rels := rels) (e.symm x) := rfl

end ToGroup

instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

end PresentedGroup
