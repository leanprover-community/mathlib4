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

@[simp]
lemma ObjectProperty.essImage_ι {C : Type*} [Category* C] (P : ObjectProperty C) :
    P.ι.essImage = P.isoClosure :=
  le_antisymm (fun _ ⟨Y, ⟨e⟩⟩ ↦ ⟨Y.obj, Y.property, ⟨e.symm⟩⟩)
    fun _ ⟨_, h, ⟨e⟩⟩ ↦ ⟨⟨_, h⟩, ⟨e.symm⟩⟩

lemma Limits.PreservesFilteredColimitsOfSize.of_iso {F F' : C ⥤ D}
    [PreservesFilteredColimitsOfSize.{t, w} F] (e : F ≅ F') :
    PreservesFilteredColimitsOfSize.{t, w} F' :=
  ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso (J := J) e⟩

lemma Limits.PreservesFilteredColimitsOfSize.iff_of_iso {F F' : C ⥤ D}
    [PreservesFilteredColimitsOfSize.{t, w} F] (e : F ≅ F') :
    PreservesFilteredColimitsOfSize.{t, w} F ↔ PreservesFilteredColimitsOfSize.{t, w} F' :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

lemma Functor.isLeftKanExtension_of_iso' {C H D : Type*} [Category* C] [Category* H] [Category* D]
    {F : D ⥤ H} {L L' : C ⥤ D} {G : C ⥤ H} (e : L ≅ L') (α : G ⟶ L ⋙ F) (α' : G ⟶ L' ⋙ F)
    (comm : α ≫ Functor.whiskerRight e.hom _ = α') [F.IsLeftKanExtension α] :
    F.IsLeftKanExtension α' := by
  rw [← Functor.isLeftKanExtension_iff_postcompose (L := L) (L' := 𝟭 _) (L'' := L') α
    (Functor.rightUnitor _ ≪≫ e) (Functor.leftUnitor _).hom α']
  infer_instance

/-- Let `F` be a left-extension of `G` along `L ⋙ L'` and `d : D`. The cocone of `F` as an extension
along `L` at `d` is isomorphic to the whiskered cocone of `F` at `d`. -/
def Functor.LeftExtension.coconeAtPostcomp₁Iso {C H D D' : Type*} [Category* C] [Category* H]
    [Category* D] [Category* D']
    {L : C ⥤ D} {L' : D ⥤ D'} {G : C ⥤ H} (F : (L ⋙ L').LeftExtension G) (d : D) :
    ((LeftExtension.postcomp₁ L' (𝟙 (L ⋙ L')) G).obj F).coconeAt d ≅
      Cocone.whisker (CostructuredArrow.post L L' d) (F.coconeAt (L'.obj d)) :=
  Cocone.ext (Iso.refl _) fun j ↦ by simp

/-- If `F` is the pointwise left Kan extension of `G` along `L ⋙ L'` and `L'` is fully faithful,
then `L' ⋙ F` is the pointwise left Kan extension of `G` along `L`. -/
def Functor.LeftExtension.IsPointwiseLeftKanExtension.postcomp₁ {C H D D' : Type*}
    [Category* C] [Category* H] [Category* D] [Category* D']
    {L : C ⥤ D} {L' : D ⥤ D'} {G : C ⥤ H}
    (F : (L ⋙ L').LeftExtension G) [L'.Full] [L'.Faithful]
    (h : F.IsPointwiseLeftKanExtension) :
    ((LeftExtension.postcomp₁ L' (𝟙 _) G).obj F).IsPointwiseLeftKanExtension := by
  intro d
  refine .ofIsoColimit ?_ (Functor.LeftExtension.coconeAtPostcomp₁Iso F d).symm
  exact (Functor.Final.isColimitWhiskerEquiv _ _).symm (h _)

lemma Functor.isLeftKanExtension_comp_left {C H D D' : Type*} [Category* C] [Category* H]
    [Category* D] [Category* D'] {F : D' ⥤ H} {L : C ⥤ D} {L' : D ⥤ D'}
    {G : C ⥤ H} [L'.Faithful] [L'.Full]
    (α : G ⟶ (L ⋙ L') ⋙ F) [F.IsLeftKanExtension α] [(L ⋙ L').HasPointwiseLeftKanExtension G] :
    (L' ⋙ F).IsLeftKanExtension (α ≫ (Functor.associator _ _ _).hom) := by
  let e : (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
    isPointwiseLeftKanExtensionOfIsLeftKanExtension F α
  convert e.postcomp₁.isLeftKanExtension
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
lemma Functor.HasPointwiseLeftKanExtension.of_iso {C H D : Type*} [Category* C] [Category* H]
    [Category* D] {L L' : C ⥤ D} {F F' : C ⥤ H}
    [L.HasPointwiseLeftKanExtension F] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseLeftKanExtension F' := by
  intro Y
  dsimp only [HasPointwiseLeftKanExtensionAt]
  let e : CostructuredArrow.proj L' Y ⋙ F' ≅
      CostructuredArrow.map₂ ((Functor.leftUnitor _).hom ≫ e₁.hom ≫ (Functor.rightUnitor _).inv)
      (𝟙 _) ⋙
      CostructuredArrow.proj L Y ⋙ F :=
    NatIso.ofComponents (fun X ↦ (e₂.app _).symm)
  rw [hasColimit_iff_of_iso e]
  infer_instance

lemma Functor.HasPointwiseLeftKanExtension.iff_of_iso {C H D : Type*} [Category* C] [Category* H]
    [Category* D] {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L.HasPointwiseLeftKanExtension F ↔ L'.HasPointwiseLeftKanExtension F' :=
  ⟨fun _ ↦ .of_iso e₁ e₂, fun _ ↦ .of_iso e₁.symm e₂.symm⟩

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.IsDense] :
    Functor.IsLeftKanExtension (𝟭 D) (Functor.rightUnitor F).inv :=
  ((Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension F).mp ‹_›).some.isLeftKanExtension

lemma Functor.DenseAt.hasPointwiseLeftKanExtensionAt {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (X : D) (hf : F.DenseAt X) :
    F.HasPointwiseLeftKanExtensionAt F X :=
  ⟨_, hf⟩

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.IsDense] :
    F.HasPointwiseLeftKanExtension F :=
  fun X ↦ (Functor.IsDense.isDenseAt F X).some.hasPointwiseLeftKanExtensionAt

/-- If `F` is dense, the left Kan extension of `F` along `F` is isomorphic to the identity. -/
def Functor.IsDense.leftKanExtensionIso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    [F.IsDense] : F.leftKanExtension F ≅ 𝟭 D :=
  Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]
lemma Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫ F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom =
      F.rightUnitor.inv := by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]
lemma Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫ (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
      F.rightUnitor.inv.app _ :=
  congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

instance {C D H : Type*} [Category* C] [Category* D] [Category* H] (L : C ⥤ D)
    [∀ (G : C ⥤ H), L.HasPointwiseLeftKanExtension G] [L.Full] [L.Faithful] :
    (L.lan : _ ⥤ D ⥤ H).Full :=
  (L.lanAdjunction _).fullyFaithfulLOfIsIsoUnit.full

instance {C D H : Type*} [Category* C] [Category* D] [Category* H] (L : C ⥤ D)
    [∀ (G : C ⥤ H), L.HasPointwiseLeftKanExtension G] [L.Full] [L.Faithful] :
    (L.lan : _ ⥤ D ⥤ H).Faithful :=
  (L.lanAdjunction _).fullyFaithfulLOfIsIsoUnit.faithful

namespace Ind

/-- The equivalence of categories induced by `Ind.inclusion : Ind C ⥤ Cᵒᵖ ⥤ Type v`. -/
@[simps! functor]
noncomputable def costructuredArrowEquivalence (X : Ind C) :
    CostructuredArrow Ind.yoneda X ≌ CostructuredArrow yoneda X.obj :=
  (Functor.asEquivalence (CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X)).trans
    (CostructuredArrow.mapNatIso yonedaCompInclusion)

instance [HasFilteredColimitsOfSize.{v₁, v₁} D] (X : Ind C) :
    HasColimitsOfShape (CostructuredArrow Ind.yoneda X) D :=
  Functor.Final.hasColimitsOfShape_of_final (E := D)
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse)

instance (F : Ind C ⥤ D) [PreservesFilteredColimitsOfSize.{v₁, v₁} F] (X : Ind C) :
    PreservesColimitsOfShape (CostructuredArrow Ind.yoneda X) F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse) _

/-- `yoneda` is dense: Every `X : Cᵒᵖ ⥤ Type v` is the colimit over
`CostructuredArrow.proj yoneda X ⋙ yoneda`. -/
def _root_.CategoryTheory.denseAtYoneda (X : Cᵒᵖ ⥤ Type v₁) : yoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone X

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

attribute [local instance] preservesColimitsOfSize_rightOp

instance : PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda X.obj) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda
    ((Ind.inclusion (C := C)).obj X)) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

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
      apply Functor.isLeftKanExtension_of_iso' iso γ γ'
      rfl
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
