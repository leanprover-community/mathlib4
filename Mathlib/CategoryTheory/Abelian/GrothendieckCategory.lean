/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A `GrothendieckCategory` is an abelian category provided that it has `AB5` and a separator.

## Theorems

Relevant implications of `GrothendieckCategory` are established in `GrothendieckCategory.hasLimits`
and `GrothendieckCategory.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

namespace CategoryTheory

open Limits

universe w v u w₂ v₂ u₂
variable (C : Type u) [Category.{v} C] (D : Type u₂) [Category.{v₂} D]

/--
In the literature, an abelian category `C` is called a Grothendieck category provided that it has
`AB5` and a separator (see `HasSeparator`).

`IsGrothendieckAbelian C` is defined such that it holds if and only if `C` is equivalent to a
Grothendieck category -- more concretely, if and only if `ShrinkHoms.{w} C` is a Grothendieck
category.
-/
@[stacks 079B]
class IsGrothendieckAbelian : Prop where
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C := by infer_instance
  ab5OfSize : AB5OfSize.{w, w} C := by infer_instance
  hasSeparator : HasSeparator C := by infer_instance

attribute [instance] IsGrothendieckAbelian.locallySmall
  IsGrothendieckAbelian.hasFilteredColimitsOfSize IsGrothendieckAbelian.ab5OfSize
  IsGrothendieckAbelian.hasSeparator

universe v' u' v₁ u₁ in
theorem comp_const (J : Type u') [Category.{v'} J] (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] (F : C ⥤ D) :
    F ⋙ Functor.const J = Functor.const J ⋙ (whiskeringRight J C D).obj F := by
  apply Functor.ext
  · intro X Y f
    simp only [Functor.comp_obj, Functor.comp_map, whiskeringRight_obj_obj,
    whiskeringRight_obj_map]
    apply NatTrans.ext
    ext x
    simp only [Functor.const_obj_obj, Functor.const_map_app, NatTrans.comp_app, Functor.comp_obj,
      eqToHom_app, eqToHom_refl, whiskerRight_app, Category.comp_id, Category.id_comp]
  · intro X
    simp only [Functor.comp_obj, whiskeringRight_obj_obj]
    apply Functor.ext
    · intro A B g
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj, eqToHom_refl,
        Functor.comp_map, Functor.map_id, Category.comp_id]
    · simp only [Functor.const_obj_obj, Functor.comp_obj]
      intros ; trivial

universe v' u' v₁ u₁ in
theorem blub (J : Type u') [Category.{v'} J] (C : Type u₁) [Category.{v₁} C] (D : Type u₂)
    [Category.{v₂} D] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] (F : C ≌ D) :
    have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence F.inverse
    HasExactColimitsOfShape J D := by
  have : HasColimitsOfShape J D := Adjunction.hasColimitsOfShape_of_equivalence F.inverse
  refine ⟨⟨?_⟩⟩
  intro I instI finI
  refine ⟨?_⟩
  intro K
  let this : (J ⥤ D) ⥤ D := F.congrRight.inverse ⋙ (colim : (J ⥤ C) ⥤ C) ⋙ F.functor
  refine preservesLimit_of_natIso K (?_ : this ≅ colim)
  unfold this
  refine Adjunction.natIsoOfRightAdjointNatIso ?_ CategoryTheory.Limits.colimConstAdj (Iso.refl _)
  have : Functor.const J ≅ F.inverse ⋙ Functor.const J ⋙ F.congrRight.functor := by
    rw [← Functor.assoc, comp_const, Equivalence.congrRight_functor, Functor.assoc]
    change Functor.const J ⋙ 𝟭 _ ≅ _
    apply isoWhiskerLeft
    rw [whiskeringRight_obj_comp]
    exact (whiskeringRight J D D).mapIso F.counitIso.symm
  apply Adjunction.ofNatIsoRight _ this.symm
  conv => lhs ; rw [← Functor.assoc]
  refine Adjunction.comp ?_ F.toAdjunction
  refine Adjunction.comp F.congrRight.symm.toAdjunction ?_
  exact CategoryTheory.Limits.colimConstAdj

variable {C} {D} in
theorem IsGrothendieckAbelian.of_equivalence
    [IsGrothendieckAbelian.{w} C] (α : C ≌ D) : IsGrothendieckAbelian.{w} D := by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact blub _ C D α
  · exact HasSeparator.of_equivalence α

instance IsGrothendieckAbelian.shrinkHoms [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
  IsGrothendieckAbelian.of_equivalence <| ShrinkHoms.equivalence C

section Instances

variable [Abelian C] [IsGrothendieckAbelian C]

instance IsGrothendieckAbelian.hasColimits : HasColimits C := has_colimits_of_finite_and_filtered
instance IsGrothendieckAbelian.hasLimits : HasLimits C := hasLimits_of_hasColimits_of_hasSeparator

end Instances

end CategoryTheory
