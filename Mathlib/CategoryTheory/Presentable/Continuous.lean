/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Presheaf
import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Type

/-!
# `κ`-continuous functors

Given categories `C`, `D` and a regular cardinal `κ : Cardinal.{w}`, we define
`isCardinalContinuous C D κ : ObjectProperty (C ⥤ D)` as the property
of functors which preserves limits indexed by categories `J`
such that `HasCardinalLT (Arrow J) κ`.

We show that if `C` is an essentially `w`-small category, then
the category of `κ`-continuous functors `Cᵒᵖ ⥤ Type w` is locally
`κ`-presentable. This is done by showing that `κ`-continuous
functors `Cᵒᵖ ⥤ Type w` are exactly the objects that are local with
respect to a suitable `w`-small family of morphisms.

## TODO (@joelriou)
* Show that any locally `κ`-presentable category is equivalent to
a category of `κ`-continuous presheaves.

-/

universe w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

namespace Functor

section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (C D) in
def isCardinalContinuous (κ : Cardinal.{w}) [Fact κ.IsRegular] : ObjectProperty (C ⥤ D) :=
  ⨅ (J : Type w) (_ : Category.{w} J) (_ : HasCardinalLT (Arrow J) κ),
    preservesLimitsOfShape C D J

lemma isCardinalContinuous_iff (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalContinuous C D κ F ↔
      ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
        PreservesLimitsOfShape J F := by
  simp [isCardinalContinuous]

lemma isCardinalContinuous.preservesColimitsOfShape {F : C ⥤ D}
    {κ : Cardinal.{w}} [Fact κ.IsRegular] (hF : isCardinalContinuous C D κ F)
    (J : Type w) [SmallCategory.{w} J] (hκ : HasCardinalLT (Arrow J) κ) :
    PreservesLimitsOfShape J F :=
  (isCardinalContinuous_iff F κ).1 hF J hκ

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalContinuous C D κ).IsClosedUnderIsomorphisms := by
  dsimp only [isCardinalContinuous]
  infer_instance

@[simp]
lemma isCardinalContinuous_precomp_iff {C' : Type u''} [Category.{v''} C']
    (G : C' ⥤ C) [G.IsEquivalence] (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalContinuous C' D κ (G ⋙ F) ↔ isCardinalContinuous C D κ F := by
  simp only [isCardinalContinuous_iff]
  refine forall_congr' (fun J ↦ forall_congr' (fun _ ↦ forall_congr' (fun hκ ↦ ?_)))
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso _ ≪≫ F.leftUnitor
  exact preservesLimitsOfShape_of_natIso e

def isCardinalContinuousCongrLeft {C' : Type u'} [Category.{v'} C']
    (e : C ≌ C') (D : Type u'') [Category.{v''} D]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalContinuous C D κ).FullSubcategory ≌
      (isCardinalContinuous C' D κ).FullSubcategory :=
  e.congrLeft.congrFullSubcategory (by aesop)

end

end Functor

namespace Presheaf

open Functor

section Small

variable (C : Type w) [SmallCategory C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

abbrev isCardinalContinuousMorphismProperty : MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  ⨆ (J) (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ),
    MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F)

example : MorphismProperty.IsSmall.{w}
    (isCardinalContinuousMorphismProperty C κ) := by
  infer_instance

lemma isCardinalContinuous_eq_isLocal :
    isCardinalContinuous Cᵒᵖ (Type w) κ =
      (isCardinalContinuousMorphismProperty.{w} C κ).isLocal := by
  trans ⨅ (J : SmallCategoryCardinalLT κ),
    preservesLimitsOfShape Cᵒᵖ (Type w) (SmallCategoryCardinalLT.categoryFamily κ J)
  · refine le_antisymm ?_ ?_
    · simp only [le_iInf_iff]
      intro J P hP
      simpa using hP.preservesColimitsOfShape _ (SmallCategoryCardinalLT.hasCardinalLT κ J)
    · dsimp [isCardinalContinuous]
      simp only [le_iInf_iff]
      intro J _ hJ
      obtain ⟨J', ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
      rw [← congr_preservesLimitsOfShape _ _ e]
      apply iInf_le
  · simp [preservesLimitsOfShape_eq_isLocal]

instance (X : C) : IsCardinalPresentable (shrinkYoneda.{w}.obj X) κ where
  preservesColimitOfShape J _ := ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f₁ f₂ hf ↦ ?_)
    · obtain ⟨x, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
      obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc) x
      exact ⟨j, shrinkYonedaEquiv.symm y,
        shrinkYonedaEquiv.injective (by simp [shrinkYonedaEquiv_comp])⟩
    · obtain ⟨x₁, rfl⟩ := shrinkYonedaEquiv.symm.surjective f₁
      obtain ⟨x₂, rfl⟩ := shrinkYonedaEquiv.symm.surjective f₂
      dsimp at hf ⊢
      rw [shrinkYonedaEquiv_symm_comp, shrinkYonedaEquiv_symm_comp] at hf
      simp only [EmbeddingLike.apply_eq_iff_eq] at hf
      obtain ⟨l, a, hl⟩ := (Types.FilteredColimit.isColimit_eq_iff'
          (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc) x₁ x₂).1 hf
      dsimp at hl
      refine ⟨l, a, ?_⟩
      rw [shrinkYonedaEquiv_symm_comp, shrinkYonedaEquiv_symm_comp, hl]⟩⟩⟩

instance (J : SmallCategoryCardinalLT κ)
    (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ) :
    IsCardinalPresentable (preservesLimitHomFamilySrc F) κ := by
  apply (config := { allowSynthFailures := true }) isCardinalPresentable_of_isColimit
    _ (colimit.isColimit (F.leftOp ⋙ shrinkYoneda.{w}))
  · simpa using J.prop
  · intro
    dsimp
    infer_instance

instance (J : SmallCategoryCardinalLT κ)
    (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ) (hF) :
    IsCardinalPresentable (preservesLimitHomFamilyTgt F hF) κ := by
  dsimp [preservesLimitHomFamilyTgt]
  infer_instance

instance : IsCardinalLocallyPresentable
    (isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory κ := by
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isLocallyPresentable_isLocal
  intro _ _ f hf
  simp only [isCardinalContinuousMorphismProperty, MorphismProperty.iSup_iff] at hf
  obtain ⟨J, F, ⟨hF⟩⟩ := hf
  constructor <;> infer_instance

end Small

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable
      (isCardinalContinuous C (Type w) κ).FullSubcategory κ :=
  (isCardinalContinuousCongrLeft ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans
    (opOpEquivalence C)) (Type w) κ).isCardinalLocallyPresentable κ

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsLocallyPresentable.{w} (isCardinalContinuous C (Type w) κ).FullSubcategory where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end Presheaf

end CategoryTheory
