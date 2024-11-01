/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Finite limits of ind-objects

-/

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C) (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda)))

noncomputable def indLim : (I ⥤ C) ⥤ (Cᵒᵖ ⥤ Type v) := (whiskeringRight _ _ _).obj yoneda ⋙ colim

include hF in
theorem isIndObject : IsIndObject (limit (F ⋙ indLim)) := by
  let bifunctor : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (whiskeringRight _ _ _).obj yoneda
  let iso : colimit (limit bifunctor) ≅ limit (colimit bifunctor.flip) := sorry
  let i : F ⋙ indLim ≅ colimit (bifunctor.flip) := (colimitFlipIsoCompColim bifunctor).symm
  apply IsIndObject.map (HasLimit.isoOfNatIso i).inv
  apply IsIndObject.map iso.hom
  apply isIndObject_colimit
  intro i
  dsimp [bifunctor]
  apply IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv
  exact hF i

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

theorem aboutParallelPairs {A B : Cᵒᵖ ⥤ Type v} (hA : IsIndObject A)
    (hB : IsIndObject B) (f g : A ⟶ B) : Nonempty (CommonMorphismPresentation f g) := sorry

theorem isIndObject_limit_of_hasLimit {J : Type} [SmallCategory J] (F : J ⥤ C) [HasLimit F] :
    IsIndObject (limit (F ⋙ yoneda)) :=
  IsIndObject.map (preservesLimitIso yoneda F).hom (isIndObject_yoneda (limit F))

theorem closed [HasEqualizers C] :
    ClosedUnderLimitsOfShape WalkingParallelPair (IsIndObject (C := C)) := by
  apply closedUnderLimitsOfShape_of_limit (fun e => IsIndObject.map e.hom)
  intro F hF h
  have :=
  aboutParallelPairs (h WalkingParallelPair.zero) (h WalkingParallelPair.one)
    (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right)
  rcases this with ⟨⟨⟩⟩
  rename_i I _ _ F₁ F₂ ι₁ isColimit₁ ι₂ isColimit₂ φ ψ hf hg
  let G : WalkingParallelPair ⥤ I ⥤ C := parallelPair φ ψ
  have := isIndObject G (fun i => isIndObject_limit_of_hasLimit _)
  suffices G ⋙ indLim ≅ F from IsIndObject.map (HasLimit.isoOfNatIso this).hom ‹_›
  refine parallelPair.ext ?_ ?_ ?_ ?_
  · exact (colimit.isColimit _).coconePointUniqueUpToIso isColimit₁
  · exact (colimit.isColimit _).coconePointUniqueUpToIso isColimit₂
  · simp only [indLim, Functor.comp_obj, parallelPair_obj_zero, whiskeringRight_obj_obj, colim_obj,
      parallelPair_obj_one, Functor.comp_map, parallelPair_map_left, whiskeringRight_obj_map,
      colim_map, G]
    apply colimit.hom_ext (fun i => ?_)
    rw [ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, hf,
      IsColimit.ι_map]
  · simp only [indLim, Functor.comp_obj, parallelPair_obj_zero, whiskeringRight_obj_obj, colim_obj,
      parallelPair_obj_one, Functor.comp_map, parallelPair_map_right, whiskeringRight_obj_map,
      colim_map, G]
    apply colimit.hom_ext (fun i => ?_)
    rw [ι_colimMap_assoc, colimit.comp_coconePointUniqueUpToIso_hom,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, hg,
      IsColimit.ι_map]

end CategoryTheory.Limits
