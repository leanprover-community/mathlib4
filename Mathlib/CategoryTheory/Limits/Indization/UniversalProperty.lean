/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Universal property of `Ind C`

Let `C` be a category and `D` a category with filtered colimits. Then
any functor `C ⥤ D` left Kan extends to a filtered colimit preserving functor `Ind C ⥤ D`.
This extension is unique in the sense that it induces an equivalence
of categories of `C ⥤ D` with the full subcategory of filtered-colimit preserving functors
`Ind C ⥤ D`.

## Main results

- `CategoryTheory.Ind.denseAtYoneda`: `Ind.yoneda : C ⥤ Ind C` is everywhere dense.
- `CategoryTheory.Ind.lanEquiv`: The left Kan extension functor `(C ⥤ D) ⥤ Ind C ⥤ D` along
  `Ind.yoneda` induces an equivalence of categories on the full subcategory of functors preserving
  filtered colimits.
-/

@[expose] public section

universe t w w' v₁ v₂ v u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

namespace Ind

/-- `Ind.yoneda` is dense: Every `X : Ind C` is the colimit over
`CostructuredArrow.proj Ind.yoneda X ⋙ Ind.yoneda`. -/
protected def denseAtYoneda (X : Ind C) : Ind.yoneda.DenseAt X := by
  refine isColimitOfReflects (Ind.inclusion C) ?_
  refine IsColimit.equivOfNatIsoOfIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ Ind.yonedaCompInclusion).symm _ _ ?_
    ((denseAtYoneda X.obj).whiskerEquivalence X.costructuredArrowEquivalence)
  refine Cocone.ext (Iso.refl _) fun j ↦ ?_
  dsimp [costructuredArrowEquivalence]
  simp only [Category.id_comp]
  apply Category.comp_id

instance : (Ind.yoneda (C := C)).IsDense where
  isDenseAt X := ⟨X.denseAtYoneda⟩

attribute [local instance] preservesColimitsOfSize_rightOp in
set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [Ind.yoneda.HasPointwiseLeftKanExtension F] :
    PreservesFilteredColimitsOfSize.{v₁, v₁} (Ind.yoneda.leftKanExtension F) where
  preserves_filtered_colimits J _ _ := by
    let D' : Type _ := (D ⥤ Type (max u₁ u₂ v₁ v₂))ᵒᵖ
    let i : D ⥤ D' := uliftCoyoneda.{max u₁ u₂ v₁ v₂}.rightOp
    suffices PreservesColimitsOfShape J (Ind.yoneda.leftKanExtension F ⋙ i) from
      preservesColimitsOfShape_of_reflects_of_preserves _ i
    let u : (Cᵒᵖ ⥤ Type v₁) ⥤ (Cᵒᵖ ⥤ Type max u₁ u₂ v₁ v₂) :=
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max u₁ u₂ v₁ v₂}
    let j : Ind.yoneda ⋙ Ind.inclusion C ≅ yoneda := Ind.yonedaCompInclusion
    let iso : uliftYoneda.{max u₁ u₂ v₁ v₂} ≅ Ind.yoneda ⋙ Ind.inclusion C ⋙ u :=
      Functor.isoWhiskerRight j.symm _ ≪≫ Functor.associator _ _ _
    have : (Ind.yoneda ⋙ Ind.inclusion C ⋙ u).HasPointwiseLeftKanExtension (F ⋙ i) :=
      Functor.HasPointwiseLeftKanExtension.of_iso iso (Iso.refl _)
    let H : (Cᵒᵖ ⥤ Type _) ⥤ D' :=
      Functor.leftKanExtension uliftYoneda.{max u₁ u₂ v₁ v₂} (F ⋙ i)
    let α : F ⋙ i ⟶ Ind.yoneda ⋙ (Ind.inclusion C ⋙ u ⋙ H) :=
      (uliftYoneda.{max u₁ u₂ v₁ v₂}).leftKanExtensionUnit (F ⋙ i) ≫
        (Functor.associator _ _ _).hom ≫
          (Functor.isoWhiskerRight Ind.yonedaCompInclusion _).inv ≫
          (Functor.associator _ _ _).hom
    let γ : F ⋙ i ⟶ (uliftYoneda.{max u₁ u₂ v₁ v₂}) ⋙ H :=
      (uliftYoneda.{max u₁ u₂ v₁ v₂}).leftKanExtensionUnit (F ⋙ i)
    let γ' : F ⋙ i ⟶ (Ind.yoneda ⋙ (Ind.inclusion C ⋙ u)) ⋙ H :=
      γ ≫ (Functor.isoWhiskerRight j (u ⋙ H)).inv
    have hγ : H.IsLeftKanExtension γ := by
      dsimp [γ', H]
      infer_instance
    let iso : uliftYoneda.{max u₁ u₂ v₁ v₂, v₁, u₁} ≅ (Ind.yoneda ⋙ Ind.inclusion C) ⋙ u :=
      Functor.isoWhiskerRight j.symm _
    have hγ' : H.IsLeftKanExtension γ' := by
      dsimp [γ', H]
      exact .of_iso₃ (.refl _) iso (.refl _) γ γ' rfl
    have hα : (Ind.inclusion C ⋙ u ⋙ H).IsLeftKanExtension α :=
      -- this is abusing some associator def-eqs
      Functor.isLeftKanExtension_comp_left γ'
    let β' : F ⟶ Ind.yoneda ⋙ Ind.yoneda.leftKanExtension F :=
      Functor.leftKanExtensionUnit _ _
    let β : F ⋙ i ⟶ Ind.yoneda ⋙ Ind.yoneda.leftKanExtension F ⋙ i :=
      (Functor.whiskerRight β' i) ≫
        (Functor.associator _ _ _).hom
    have hβ : Functor.IsLeftKanExtension (Ind.yoneda.leftKanExtension F ⋙ i) β := by
      dsimp [β]
      infer_instance
    have : PreservesColimitsOfSize.{v₁, v₁} H :=
      Presheaf.preservesColimitsOfSize_leftKanExtension.{max u₁ u₂ v₁} (F ⋙ i)
    let e : Ind.yoneda.leftKanExtension F ⋙ i ≅ Ind.inclusion C ⋙
        (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max u₁ u₂ v₁ v₂} ⋙ H :=
      Functor.leftKanExtensionUnique (Ind.yoneda.leftKanExtension F ⋙ i) β _ α
    exact preservesColimitsOfShape_of_natIso e.symm

section

/-- The left Kan extension functor along `Ind.yoneda : C ⥤ Ind C`. -/
abbrev lan [HasFilteredColimitsOfSize.{v₁, v₁} D] : (C ⥤ D) ⥤ Ind C ⥤ D :=
  Ind.yoneda.lan

variable [HasFilteredColimitsOfSize.{v₁, v₁} D]

/-- Left Kan extension along `Ind.yoneda : C ⥤ Ind C` is left-adjoint to the restriction. -/
abbrev lanAdjunction : Ind.lan ⊣ (Functor.whiskeringLeft C _ D).obj Ind.yoneda :=
  Ind.yoneda.lanAdjunction D

instance (F : C ⥤ D) : PreservesFilteredColimitsOfSize.{v₁, v₁} (Ind.lan.obj F) := by
  dsimp [Ind.lan, Functor.lan]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If `D` has filtered colimits, left Kan extension along `Ind.yoneda : C ⥤ Ind C` induces
an equivalence of categories onto the full subcategory of `C ⥤ D` consisting
of filtered-colimit preserving functors. -/
@[simps! functor inverse unitIso_hom]
def lanEquiv :
    C ⥤ D ≌ ObjectProperty.FullSubcategory
      (fun (G : Ind C ⥤ D) ↦ PreservesFilteredColimitsOfSize.{v₁, v₁} G) where
  functor := ObjectProperty.lift _ lan fun F ↦ inferInstance
  inverse := ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj Ind.yoneda
  unitIso := asIso (Ind.yoneda.lanAdjunction D).unit
  counitIso := by
    refine NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ ?_) ?_
    · haveI : PreservesFilteredColimitsOfSize F.obj := F.property
      refine ((Functor.lanCompIsoOfPreserves F.obj (Ind.yoneda (C := C))).app Ind.yoneda).symm ≪≫ ?_
      exact Functor.isoWhiskerRight (Functor.IsDense.leftKanExtensionIso Ind.yoneda) _ ≪≫
        Functor.leftUnitor _
    · intro F G f
      ext : 1
      apply Functor.hom_ext_of_isLeftKanExtension _ (Functor.leftKanExtensionUnit _ _)
      ext
      simp [Functor.lan]
  functor_unitIso_comp G := by
    ext : 1
    apply Functor.hom_ext_of_isLeftKanExtension _ (Functor.leftKanExtensionUnit _ _)
    ext
    simp [Functor.lan, Functor.lanUnit, ← Functor.map_comp]

variable (C D) in
lemma essImage_lan_eq_preservesFilteredColimitsOfSize : (Ind.lan (C := C) (D := D)).essImage =
    (PreservesFilteredColimitsOfSize.{v₁, v₁} ·) := by
  ext F
  exact ⟨fun ⟨G, ⟨i⟩⟩ ↦ .of_iso i,
    fun h ↦ ⟨Ind.yoneda ⋙ F, ⟨(ObjectProperty.ι _).mapIso (lanEquiv.counitIso.app ⟨F, h⟩)⟩⟩⟩

end

end Ind

end CategoryTheory
