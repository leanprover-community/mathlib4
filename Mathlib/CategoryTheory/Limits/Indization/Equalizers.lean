/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Indization.Morphisms

/-!
# Equalizers of ind-objects

The eventual goal of this file is to show that if a category `C` has equalizers, then ind-objects
are closed under equalizers. For now, it contains one of the main prerequisites, namely we show
that under sufficient conditions the limit of a diagram in `I ⥤ C` taken in `Cᵒᵖ ⥤ Type v` is an
ind-object.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 6.1
-/

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C)

/--
Suppose `F : J ⥤ I ⥤ C` is a finite diagram in the functor category `I ⥤ C`, where `I` is small
and filtered. If `i : I`, we can apply the Yoneda embedding to `F(·, i)` to obtain a
diagram of presheaves `J ⥤ Cᵒᵖ ⥤ Type v`. Suppose that the limits of this diagram is always an
ind-object.

For `j : J` we can apply the Yoneda embedding to `F(j, ·)` and take colimits to obtain a finite
diagram `J ⥤ Cᵒᵖ ⥤ Type v` (which is actually a diagram `J ⥤ Ind C`). The theorem states that
the limit of this diagram is an ind-object.

This theorem will be used to construct equalizers in the category of ind-objects. It can be
interpreted as saying that ind-objects are closed under finite limits as long as the diagram
we are taking the limit of comes from a diagram in a functor category `I ⥤ C`. We will show (TODO)
that this is the case for any parallel pair of morphisms in `Ind C` and deduce that ind-objects
are closed under equalizers.

This is Proposition 6.1.16(i) in [Kashiwara2006].
-/
theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)

end

structure CommonMorphismPresentation {A B : Cᵒᵖ ⥤ Type v} (f g : A ⟶ B) where
  I : Type v
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  F₁ : I ⥤ C
  F₂ : I ⥤ C
  ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
  isColimit₁ : IsColimit (Cocone.mk A ι₁)
  ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
  isColimit₂ : IsColimit (Cocone.mk B ι₂)
  φ : F₁ ⟶ F₂
  ψ : F₁ ⟶ F₂
  hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)
  hg : g = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight ψ yoneda)

theorem isIndObject_limit_of_hasLimit {J : Type} [SmallCategory J] (F : J ⥤ C) [HasLimit F] :
    IsIndObject (limit (F ⋙ yoneda)) :=
  IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

theorem closed [HasEqualizers C] :
    ClosedUnderLimitsOfShape WalkingParallelPair (IsIndObject (C := C)) := by
  apply closedUnderLimitsOfShape_of_limit --(fun e => IsIndObject.map e.hom)
  intro F hF h
  have :=
  aboutParallelPairs (h WalkingParallelPair.zero) (h WalkingParallelPair.one)
    (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right)
  rcases this with ⟨⟨⟩⟩
  rename_i I _ _ F₁ F₂ ι₁ isColimit₁ ι₂ isColimit₂ φ ψ hf hg
  let G : WalkingParallelPair ⥤ I ⥤ C := parallelPair φ ψ
  have := isIndObject_limit_comp_yoneda_comp_colim G (fun i => isIndObject_limit_of_hasLimit _)
  suffices G ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim ≅ F from
    IsIndObject.map (HasLimit.isoOfNatIso this).hom ‹_›
  refine parallelPair.ext ?_ ?_ ?_ ?_
  · exact (colimit.isColimit _).coconePointUniqueUpToIso isColimit₁
  · exact (colimit.isColimit _).coconePointUniqueUpToIso isColimit₂
  · simp only [Functor.comp_obj, parallelPair_obj_zero, whiskeringRight_obj_obj, colim_obj,
      parallelPair_obj_one, Functor.comp_map, parallelPair_map_left, whiskeringRight_obj_map,
      colim_map, G]
    apply colimit.hom_ext (fun i => ?_)
    rw [ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, hf,
      IsColimit.ι_map]
  · simp only [Functor.comp_obj, parallelPair_obj_zero, whiskeringRight_obj_obj, colim_obj,
      parallelPair_obj_one, Functor.comp_map, parallelPair_map_right, whiskeringRight_obj_map,
      colim_map, G]
    apply colimit.hom_ext (fun i => ?_)
    rw [ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, hg,
      IsColimit.ι_map]

end CategoryTheory.Limits
