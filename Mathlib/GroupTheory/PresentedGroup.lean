/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Newell Jensen
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

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

/-- The canonical map from the free group on `α` to a presented group with generators `x : α`,
where `x` is mapped to its equivalence class under the given set of relations `rels` -/
def mk (rels : Set (FreeGroup α)) : FreeGroup α →* PresentedGroup rels :=
  ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩

theorem mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective <| mk rels :=
  QuotientGroup.mk_surjective

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `FreeGroup α`. -/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  mk rels (FreeGroup.of x)

lemma mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} :
    mk rels x = 1 ↔ x ∈ Subgroup.normalClosure rels :=
  QuotientGroup.eq_one_iff _

lemma one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ rels) :
    mk rels x = 1 :=
  mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure hx

lemma mk_eq_mk_of_mul_inv_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x * y⁻¹ ∈ rels) : mk rels x = mk rels y :=
  eq_of_mul_inv_eq_one <| one_of_mem hx

lemma mk_eq_mk_of_inv_mul_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x⁻¹ * y ∈ rels) : mk rels x = mk rels y :=
  eq_of_inv_mul_eq_one <| one_of_mem hx

/-- The generators of a presented group generate the presented group. That is, the subgroup closure
of the set of generators equals `⊤`. -/
@[simp]
theorem closure_range_of (rels : Set (FreeGroup α)) :
    Subgroup.closure (Set.range (PresentedGroup.of : α → PresentedGroup rels)) = ⊤ := by
  have : (PresentedGroup.of : α → PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this, Set.range_comp, ← MonoidHom.map_closure (QuotientGroup.mk' _),
    FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)

@[induction_eliminator]
theorem induction_on {rels : Set (FreeGroup α)} {C : PresentedGroup rels → Prop}
    (x : PresentedGroup rels) (H : ∀ z, C (mk rels z)) : C x :=
  Quotient.inductionOn' x H

theorem generated_by (rels : Set (FreeGroup α)) (H : Subgroup (PresentedGroup rels))
    (h : ∀ j : α, PresentedGroup.of j ∈ H) (x : PresentedGroup rels) : x ∈ H := by
  obtain ⟨z⟩ := x
  induction z
  · exact one_mem H
  · exact h _
  · exact (Subgroup.inv_mem_iff H).mpr (by assumption)
  rename_i h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

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
  Subgroup.normalClosure_le_normal fun x w ↦ MonoidHom.mem_ker.2 (h x w)

theorem to_group_eq_one_of_mem_closure (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    ∀ x ∈ Subgroup.normalClosure rels, F x = 1 :=
  fun _ w ↦ MonoidHom.mem_ker.1 <| closure_rels_subset_ker h w

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `PresentedGroup rels → G`. -/
def toGroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]
theorem toGroup.of (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift_apply_of

theorem toGroup.unique (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
    (hg : ∀ x : α, g (PresentedGroup.of x) = f x) : ∀ {x}, g x = toGroup h x := by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ ↦ FreeGroup.lift_unique (g.comp (QuotientGroup.mk' _)) hg

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
