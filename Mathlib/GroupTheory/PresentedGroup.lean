/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Newell Jensen
-/
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

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

namespace PresentedGroup

instance (rels : Set (FreeGroup α)) : Group (PresentedGroup rels) :=
  QuotientGroup.Quotient.group _

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `FreeGroup α`. -/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  QuotientGroup.mk (FreeGroup.of x)

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

theorem closure_rels_subset_ker (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    Subgroup.normalClosure rels ≤ MonoidHom.ker F :=
  Subgroup.normalClosure_le_normal fun x w ↦ (MonoidHom.mem_ker _).2 (h x w)

theorem to_group_eq_one_of_mem_closure (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    ∀ x ∈ Subgroup.normalClosure rels, F x = 1 :=
  fun _ w ↦ (MonoidHom.mem_ker _).1 <| closure_rels_subset_ker h w

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `PresentedGroup rels → G`. -/
def toGroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]
theorem toGroup.of (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift.of

theorem toGroup.unique (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
    (hg : ∀ x : α, g (PresentedGroup.of x) = f x) : ∀ {x}, g x = toGroup h x := by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ ↦ FreeGroup.lift.unique (g.comp (QuotientGroup.mk' _)) hg

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
