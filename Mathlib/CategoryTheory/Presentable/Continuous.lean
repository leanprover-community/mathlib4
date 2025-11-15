/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.Presheaf
import Mathlib.CategoryTheory.Limits.FullSubcategory
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

lemma isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt
    ⦃X Y : Cᵒᵖ ⥤ Type w⦄ (f : X ⟶ Y) (hf : isCardinalContinuousMorphismProperty C κ f) :
    IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ := by
  simp only [isCardinalContinuousMorphismProperty, MorphismProperty.iSup_iff] at hf
  obtain ⟨J, F, ⟨hF⟩⟩ := hf
  constructor <;> infer_instance

instance : IsCardinalLocallyPresentable
    (isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory κ := by
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isLocallyPresentable_isLocal
  apply isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt

instance : (isCardinalContinuous Cᵒᵖ (Type w) κ).ι.IsRightAdjoint := by
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isRightAdjoint_ι_isLocal _ κ
  apply isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt

instance : HasLimitsOfSize.{w, w} (isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory := by
  rw [isCardinalContinuous_eq_isLocal]
  exact ⟨inferInstance⟩

variable {C κ} in
lemma isCardinalFiltered_costructuredArrow_yoneda
    {P : Cᵒᵖ ⥤ Type w} (hP : isCardinalContinuous Cᵒᵖ (Type w) κ P)
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C) :
    IsCardinalFiltered (CostructuredArrow yoneda P) κ where
  nonempty_cocone {J _} F hJ := by
    have := hC J hJ
    have := hP.preservesColimitsOfShape Jᵒᵖ (by simpa)
    let s : ((F ⋙ CostructuredArrow.proj _ _).op ⋙ P).sections :=
      { val j := yonedaEquiv (F := P) (F.obj j.unop).hom
        property {j j'} g := by
          dsimp
          rw [← CostructuredArrow.w (F.map g.unop), yonedaEquiv_naturality] }
    obtain ⟨f, hf⟩ := ((Types.isLimit_iff_bijective_sectionOfCone _).1
      ⟨isLimitOfPreserves P (colimit.isColimit _).op⟩).2 s
    replace hf (j : J) := congr_fun (congr_arg Subtype.val hf) (op j)
    dsimp [s] at hf
    exact ⟨CostructuredArrow.mk (yonedaEquiv.symm f),
      { app j := CostructuredArrow.homMk (colimit.ι (F ⋙ CostructuredArrow.proj _ _) j)
            (yonedaEquiv.injective (by simp [← hf j, yonedaEquiv_apply]))
        naturality j j' g := by
          ext
          simpa [-colimit.w] using colimit.w (F ⋙ CostructuredArrow.proj _ _) g }⟩

end Small

section EssentiallySmall

variable (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

instance : IsCardinalLocallyPresentable
      (isCardinalContinuous C (Type w) κ).FullSubcategory κ :=
  (isCardinalContinuousCongrLeft ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans
    (opOpEquivalence C)) (Type w) κ).isCardinalLocallyPresentable κ

instance : IsLocallyPresentable.{w} (isCardinalContinuous C (Type w) κ).FullSubcategory where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

instance : (isCardinalContinuous C (Type w) κ).ι.IsRightAdjoint := by
  let e := ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans (opOpEquivalence C))
  let e' := isCardinalContinuousCongrLeft e (Type w) κ
  let iso : (isCardinalContinuous C (Type w) κ).ι ≅
    e'.inverse ⋙
      (isCardinalContinuous (SmallModel.{w} Cᵒᵖ)ᵒᵖ (Type w) κ).ι ⋙ e.congrLeft.functor := by
    refine (leftUnitor _).symm ≪≫ isoWhiskerRight e'.counitIso.symm _ ≪≫ associator _ _ _ ≪≫
      isoWhiskerLeft e'.inverse (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso iso.symm

instance :
    HasLimitsOfSize.{w, w} (isCardinalContinuous C (Type w) κ).FullSubcategory :=
  Adjunction.has_limits_of_equivalence
    ((isCardinalContinuousCongrLeft ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans
      (opOpEquivalence C)) (Type w) κ).inverse)

attribute [local simp] shrinkYoneda in
@[simps!]
noncomputable def _root_.CategoryTheory.Equivalence.shrinkYonedaIsoConjugateYoneda
    {D : Type*} [Category.{w} D] (e : C ≌ D) :
    shrinkYoneda.{w} ≅ e.functor ⋙ yoneda ⋙
      (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj e.functor.op :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦
    ((equivShrink _).symm.trans e.fullyFaithfulFunctor.homEquiv).toIso))

variable {C κ} in
lemma exists_presentation_of_isCardinalContinuous
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C)
    {F : Cᵒᵖ ⥤ Type w}
    (hF : isCardinalContinuous _ _ κ F) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
      (G : J ⥤ CostructuredArrow shrinkYoneda F)
      (ι : G ⋙ CostructuredArrow.proj _ _ ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj F),
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  let C' := SmallModel.{w} C
  let e : C ≌ C' := equivSmallModel.{w} C
  replace hF : isCardinalContinuous _ _ κ (e.inverse.op ⋙ F) := by simpa
  replace hF := isCardinalFiltered_costructuredArrow_yoneda hF (fun J _ hJ ↦ by
    have := hC J hJ
    exact Adjunction.hasColimitsOfShape_of_equivalence e.inverse)
  let iso' : e.inverse ⋙ shrinkYoneda.{w} ≅ yoneda ⋙
    (whiskeringLeft Cᵒᵖ C'ᵒᵖ (Type w)).obj e.functor.op :=
      isoWhiskerLeft e.inverse e.shrinkYonedaIsoConjugateYoneda ≪≫ (associator _ _ _).symm ≪≫
        isoWhiskerRight e.counitIso _ ≪≫ leftUnitor _
  let isoF := ((associator _ _ _).symm ≪≫ isoWhiskerRight e.op.unitIso.symm F
    ≪≫ leftUnitor _)
  let G : CostructuredArrow yoneda (e.inverse.op ⋙ F) ⥤
      CostructuredArrow shrinkYoneda.{w} F :=
    CostructuredArrow.map₂ (F := e.inverse) (G := (whiskeringLeft _ _ _).obj e.functor.op)
      iso'.hom isoF.hom
  let projIso : G ⋙ CostructuredArrow.proj _ _ ≅  CostructuredArrow.proj _ _ ⋙ e.inverse :=
    Iso.refl _
  refine ⟨CostructuredArrow yoneda (e.inverse.op ⋙ F), inferInstance, hF, G, ?_, ⟨?_⟩⟩
  · refine
      { app X := shrinkYonedaEquiv.symm (yonedaEquiv X.hom)
        naturality X Y f := ?_ }
    apply shrinkYonedaEquiv.injective
    have := congr_fun (Y.hom.naturality f.left.op) (𝟙 _)
    dsimp at this
    simp only [Category.comp_id] at this
    simp [← CostructuredArrow.w f,
      -CommaMorphism.w, shrinkYoneda, yonedaEquiv, shrinkYonedaEquiv, G, this]
  · have H := isColimitOfPreserves (e.op.congrLeft (E := Type w)).inverse
      ((isColimitTautologicalCocone (e.inverse.op ⋙ F)))
    refine (IsColimit.equivOfNatIsoOfIso
      (associator _ _ _ ≪≫ isoWhiskerLeft _ iso'.symm ≪≫ (associator _ _ _).symm ≪≫
        isoWhiskerRight projIso.symm _ ≪≫ associator _ _ _) _ _ ?_).1
        (isColimitOfPreserves (e.op.congrLeft).inverse
          ((isColimitTautologicalCocone (e.inverse.op ⋙ F))))
    refine Cocones.ext isoF ?_
    intro j
    dsimp
    obtain ⟨Y, f, rfl⟩ := j.mk_surjective
    obtain ⟨y, rfl⟩ := yonedaEquiv.symm.surjective f
    ext X x
    dsimp at x
    obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
    simp [iso', isoF, projIso, shrinkYonedaEquiv]
    erw [Equiv.apply_symm_apply]
    simp [yonedaEquiv, ← FunctorToTypes.map_comp_apply, ← op_comp]

end EssentiallySmall

end Presheaf

end CategoryTheory
