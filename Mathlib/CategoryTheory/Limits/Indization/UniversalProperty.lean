module

public import Mathlib

@[expose] public section

universe t w w' v₁ v₂ v u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasFilteredColimitsOfSize.{v₁, v₁} D]

lemma Functor.isLeftKanExtension_of_iso' {C H D : Type*} [Category* C] [Category* H] [Category* D]
    {F : D ⥤ H} {L L' : C ⥤ D} {G : C ⥤ H} (e : L ≅ L') (α : G ⟶ L ⋙ F) (α' : G ⟶ L' ⋙ F)
    (comm : α ≫ Functor.whiskerRight e.hom _ = α') [F.IsLeftKanExtension α] :
    F.IsLeftKanExtension α' := by
  rw [← Functor.isLeftKanExtension_iff_postcompose (L := L) (L' := 𝟭 _) (L'' := L') α
    (Functor.rightUnitor _ ≪≫ e) (Functor.leftUnitor _).hom α']
  infer_instance

def Functor.LeftExtension.coconeAtPostcomp₁Iso {C H D D' : Type*} [Category* C] [Category* H]
    [Category* D] [Category* D']
    {L : C ⥤ D} {L' : D ⥤ D'} {G : C ⥤ H} (e : (L ⋙ L').LeftExtension G) (d : D) :
    ((LeftExtension.postcomp₁ L' (𝟙 (L ⋙ L')) G).obj e).coconeAt d ≅
      Cocone.whisker (CostructuredArrow.post L L' d) (e.coconeAt (L'.obj d)) :=
  Cocone.ext (Iso.refl _) fun j ↦ by simp

def Functor.LeftExtension.IsPointwiseLeftKanExtension.postcomp₁ {C H D D' : Type*}
    [Category* C] [Category* H] [Category* D] [Category* D']
    {L : C ⥤ D} {L' : D ⥤ D'} {G : C ⥤ H}
    (e : (L ⋙ L').LeftExtension G) [L'.Full] [L'.Faithful]
    (h : e.IsPointwiseLeftKanExtension) :
    ((LeftExtension.postcomp₁ L' (𝟙 _) G).obj e).IsPointwiseLeftKanExtension := by
  intro d
  refine .ofIsoColimit ?_ (Functor.LeftExtension.coconeAtPostcomp₁Iso e d).symm
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

namespace Ind

@[simps!]
noncomputable
def costructuredArrowEquivalence (X : Ind C) :
    CostructuredArrow Ind.yoneda X ≌ CostructuredArrow yoneda X.obj :=
  (Functor.asEquivalence (CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X)).trans
    (CostructuredArrow.mapNatIso yonedaCompInclusion)

instance (X : Ind C) : IsFiltered (CostructuredArrow Ind.yoneda X) :=
  inferInstance

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow Ind.yoneda X) D :=
  Functor.Final.hasColimitsOfShape_of_final (E := D)
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse)

instance (F : Ind C ⥤ D) [PreservesFilteredColimitsOfSize.{v₁, v₁} F] (X : Ind C) :
    PreservesColimitsOfShape (CostructuredArrow Ind.yoneda X) F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse) _

def lan : (C ⥤ D) ⥤ Ind C ⥤ D := Ind.yoneda.lan

def yonedaLanAdj : Ind.lan (C := C) (D := D) ⊣ (Functor.whiskeringLeft _ _ _).obj Ind.yoneda :=
  Ind.yoneda.lanAdjunction D

set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) : IsIso ((Ind.yonedaLanAdj (C := C) (D := D)).unit.app F) := by
  dsimp [Ind.yonedaLanAdj]
  infer_instance

instance : IsIso (Ind.yonedaLanAdj (C := C) (D := D)).unit := by
  apply NatIso.isIso_of_isIso_app

def lanFullyFaithful : (Ind.lan (C := C) (D := D)).FullyFaithful :=
  (Ind.yonedaLanAdj (C := C) (D := D)).fullyFaithfulLOfIsIsoUnit

instance : (Ind.lan (C := C) (D := D)).Full := Ind.lanFullyFaithful.full

instance : (Ind.lan (C := C) (D := D)).Faithful := Ind.lanFullyFaithful.faithful

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda
    ((Ind.inclusion (C := C)).obj X)) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda X.obj) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow Ind.yoneda X) (Ind C) := inferInstance

def _root_.CategoryTheory.denseAtYoneda (X : Cᵒᵖ ⥤ Type v₁) : yoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone X

protected def denseAtYoneda (X : Ind C) : Ind.yoneda.DenseAt X := by
  refine isColimitOfReflects (Ind.inclusion C) ?_
  refine IsColimit.equivOfNatIsoOfIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ Ind.yonedaCompInclusion).symm _ _ ?_
    ((denseAtYoneda X.obj).whiskerEquivalence X.costructuredArrowEquivalence)
  refine Cocone.ext (Iso.refl _) fun j ↦ ?_
  dsimp [costructuredArrowEquivalence]
  simp only [Category.id_comp]
  apply Category.comp_id

def isoColimit (X : Ind C) : X ≅
    colimit (CostructuredArrow.proj Ind.yoneda X ⋙ Ind.yoneda) :=
  (Ind.denseAtYoneda X).isoColimit

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_isoColimit_inv (X : Ind C) (j : CostructuredArrow Ind.yoneda X) :
    colimit.ι _ j ≫ X.isoColimit.inv = j.hom := by
  simp [isoColimit]

attribute [local instance] preservesColimitsOfSize_rightOp

instance : PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) : PreservesFilteredColimitsOfSize.{v₁, v₁} (Ind.lan.obj F) where
  preserves_filtered_colimits J _ _ := by
    let D' : Type _ := (D ⥤ Type (max u₁ u₂ v₁ v₂))ᵒᵖ
    let i : D ⥤ D' := uliftCoyoneda.{max u₁ u₂ v₁ v₂}.rightOp
    suffices PreservesColimitsOfShape J (Ind.lan.obj F ⋙ i) from
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
    let β' : F ⟶ Ind.yoneda ⋙ lan.obj F :=
      Functor.leftKanExtensionUnit _ _
    have : (lan.obj F).IsLeftKanExtension β' := by
      dsimp [β', Ind.lan, Functor.lan]
      infer_instance
    let β : F ⋙ i ⟶ Ind.yoneda ⋙ lan.obj F ⋙ i :=
      (Functor.whiskerRight β' i) ≫
        (Functor.associator _ _ _).hom
    have hβ : Functor.IsLeftKanExtension (lan.obj F ⋙ i) β := by
      dsimp [β]
      infer_instance
    have : PreservesColimitsOfSize.{v₁, v₁} H :=
      Presheaf.preservesColimitsOfSize_leftKanExtension.{max u₁ u₂ v₁} (F ⋙ i)
    let e : Ind.lan.obj F ⋙ i ≅ Ind.inclusion C ⋙
        (Functor.whiskeringRight _ _ _).obj uliftFunctor.{max u₁ u₂ v₁ v₂} ⋙ H := by
      refine Functor.leftKanExtensionUnique (Ind.lan.obj F ⋙ i) β _ α
    exact preservesColimitsOfShape_of_natIso e.symm

set_option backward.isDefEq.respectTransparency false in
lemma lanEssImage_eq_preservesFilteredColimitsOfSize : (Ind.lan (C := C) (D := D)).essImage =
    (fun G ↦ PreservesFilteredColimitsOfSize.{v₁, v₁} G) := by
  ext F
  constructor
  · intro h
    obtain ⟨G, ⟨i⟩⟩ := h
    constructor
    intro J _ _
    exact preservesColimitsOfShape_of_natIso i
  · intro h
    refine ⟨Ind.yoneda ⋙ F, ⟨?_⟩⟩
    let i : Ind.lan.obj (Ind.yoneda ⋙ F) ≅
        Functor.pointwiseLeftKanExtension Ind.yoneda (Ind.yoneda ⋙ F) :=
      Functor.leftKanExtensionUnique _
        (Functor.leftKanExtensionUnit _ _) _
        (Functor.pointwiseLeftKanExtensionUnit _ _)
    refine i ≪≫ NatIso.ofComponents (fun X ↦
      colim.mapIso (Functor.associator _ _ _).symm ≪≫
        (preservesColimitIso F _).symm ≪≫ F.mapIso X.isoColimit.symm) ?_
    intro X Y f
    apply colimit.hom_ext
    simp [← Functor.map_comp]

def universalProperty :
    ObjectProperty.FullSubcategory (C := Ind C ⥤ D)
      (fun G ↦ PreservesFilteredColimitsOfSize.{v₁, v₁} G) ≌ C ⥤ D :=
  Equivalence.trans (ObjectProperty.fullSubcategoryCongr
    (lanEssImage_eq_preservesFilteredColimitsOfSize (C := C) (D := D))).symm
    (Functor.asEquivalence ((Ind.lan (C := C) (D := D)).toEssImage)).symm

end Ind

end CategoryTheory
