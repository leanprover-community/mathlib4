/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Types.PreservesLimit
public import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.SmallRepresentatives
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# `κ`-continuous functors

Given categories `C`, `D` and a (regular) cardinal `κ : Cardinal.{w}`,
we define `isCardinalContinuous C D κ : ObjectProperty (C ⥤ D)` as
the property of functors which preserves limits indexed by categories `J`
such that `HasCardinalLT (Arrow J) κ`.

We show that if `C` is an essentially `w`-small category, then
the category of `κ`-continuous functors `Cᵒᵖ ⥤ Type w` is locally
`κ`-presentable. This is done by showing that `κ`-continuous
functors `Cᵒᵖ ⥤ Type w` are exactly the objects that are local with
respect to a suitable `w`-small family of morphisms, see the lemma
`Presheaf.isCardinalContinuous_eq_isLocal`.

## TODO (@joelriou)
* Show that any locally `κ`-presentable category is equivalent to
a category of `κ`-continuous presheaves.

-/

@[expose] public section

universe w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

namespace Functor

section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (C D) in
/-- Given a cardinal `κ`, this is the property of objects
in the category of functors `C ⥤ D` that is satisfied by `κ`-continuous
functors, i.e. functors which preserve limits indexed by categories `J`
such that `Arrow J` is of cardinality `< κ`. -/
def isCardinalContinuous (κ : Cardinal.{w}) : ObjectProperty (C ⥤ D) :=
  ⨅ (J : Type w) (_ : Category.{w} J) (_ : HasCardinalLT (Arrow J) κ),
    ObjectProperty.preservesLimitsOfShape J

lemma isCardinalContinuous_iff (F : C ⥤ D) (κ : Cardinal.{w}) :
    isCardinalContinuous C D κ F ↔
      ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
        PreservesLimitsOfShape J F := by
  simp [isCardinalContinuous]

lemma isCardinalContinuous.preservesColimitsOfShape {F : C ⥤ D}
    {κ : Cardinal.{w}} (hF : isCardinalContinuous C D κ F)
    (J : Type w) [SmallCategory.{w} J] (hκ : HasCardinalLT (Arrow J) κ) :
    PreservesLimitsOfShape J F :=
  (isCardinalContinuous_iff F κ).1 hF J hκ

instance (κ : Cardinal.{w}) :
    (isCardinalContinuous C D κ).IsClosedUnderIsomorphisms := by
  dsimp only [isCardinalContinuous]
  infer_instance

@[simp]
lemma isCardinalContinuous_precomp_iff {C' : Type u''} [Category.{v''} C']
    (G : C' ⥤ C) [G.IsEquivalence] (F : C ⥤ D) (κ : Cardinal.{w}) :
    isCardinalContinuous C' D κ (G ⋙ F) ↔ isCardinalContinuous C D κ F := by
  simp only [isCardinalContinuous_iff]
  refine forall_congr' (fun J ↦ forall_congr' (fun _ ↦ forall_congr' (fun hκ ↦ ?_)))
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso _ ≪≫ F.leftUnitor
  exact preservesLimitsOfShape_of_natIso e

def isCardinalContinuousCongrLeft {C' : Type u'} [Category.{v'} C']
    (e : C ≌ C') (D : Type u'') [Category.{v''} D] (κ : Cardinal.{w}) :
    (isCardinalContinuous C D κ).FullSubcategory ≌
      (isCardinalContinuous C' D κ).FullSubcategory :=
  e.congrLeft.congrFullSubcategory (by aesop)

end

end Functor

namespace Presheaf

open CategoryTheory.Functor

section Small

variable (C : Type w) [SmallCategory C] (κ : Cardinal.{w})

/-- Given a `w`-small category `C` and a cardinal `κ`, this is a
`w`-small family of morphisms in `Cᵒᵖ ⥤ Type w` such that `κ`-continuous
functors `Cᵒᵖ ⥤ Type w` are exactly the objects that are local with
respect to this family of morphisms,
see the lemma `isCardinalContinuous_eq_isLocal`. -/
abbrev isCardinalContinuousMorphismProperty : MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  ⨆ (J : SmallCategoryCardinalLT κ) (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ),
    MorphismProperty.ofHoms (Presheaf.preservesLimitHomFamily F)

lemma isCardinalContinuous_eq_isLocal :
    isCardinalContinuous Cᵒᵖ (Type w) κ =
      (isCardinalContinuousMorphismProperty.{w} C κ).isLocal := by
  trans ⨅ (J : SmallCategoryCardinalLT κ),
    ObjectProperty.preservesLimitsOfShape (SmallCategoryCardinalLT.categoryFamily κ J)
  · refine le_antisymm ?_ ?_
    · simp only [le_iInf_iff]
      intro J P hP
      simpa using hP.preservesColimitsOfShape _ (SmallCategoryCardinalLT.hasCardinalLT κ J)
    · dsimp [isCardinalContinuous]
      simp only [le_iInf_iff]
      intro J _ hJ
      obtain ⟨J', ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
      rw [← ObjectProperty.congr_preservesLimitsOfShape _ _ e]
      apply iInf_le
  · simp [preservesLimitsOfShape_eq_isLocal]

variable [Fact κ.IsRegular]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance (X : C) :
    IsCardinalPresentable (shrinkYoneda.{w}.obj X) κ where
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

set_option backward.defeqAttrib.useBackward true in
instance (J : SmallCategoryCardinalLT κ)
    (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ)
    (X : (SmallCategoryCardinalLT.categoryFamily κ J)ᵒᵖ) :
    IsCardinalPresentable ((F.leftOp ⋙ shrinkYoneda.{w, w, w}).obj X) κ := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (J : SmallCategoryCardinalLT κ)
    (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ) :
    IsCardinalPresentable (preservesLimitHomFamilySrc F) κ :=
  isCardinalPresentable_of_isColimit
    _ (colimit.isColimit (F.leftOp ⋙ shrinkYoneda.{w})) _
    (by simpa using J.prop)

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
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular]

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] shrinkYoneda in
@[simps!]
noncomputable def _root_.CategoryTheory.Equivalence.shrinkYonedaIsoConjugateYoneda
    {D : Type*} [Category.{w} D] (e : C ≌ D) :
    shrinkYoneda.{w} ≅ e.functor ⋙ yoneda ⋙
      (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj e.functor.op :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦
    ((equivShrink _).symm.trans e.fullyFaithfulFunctor.homEquiv).toIso))

-- to be moved?
instance (F : Cᵒᵖ ⥤ Type w) :
    EssentiallySmall.{w} (CostructuredArrow shrinkYoneda.{w} F) :=
  CostructuredArrow.essentiallySmall' ..

set_option backward.isDefEq.respectTransparency false in
lemma isCardinalFiltered_costructuredArrow_shrinkYoneda
    {P : Cᵒᵖ ⥤ Type w} (hP : isCardinalContinuous Cᵒᵖ (Type w) κ P)
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C) :
    IsCardinalFiltered (CostructuredArrow shrinkYoneda.{w} P) κ := by
  let F : CostructuredArrow yoneda ((equivSmallModel.{w} C).op.inverse ⋙ P) ⥤
      (CostructuredArrow shrinkYoneda.{w} P) :=
    CostructuredArrow.post _
      ((whiskeringLeft _ _ _).obj (equivSmallModel.{w} C).op.functor) _ ⋙
    (CostructuredArrow.mapIso
      (Functor.isoWhiskerRight (NatIso.op (equivSmallModel C).unitIso) P)).functor ⋙
    (CostructuredArrow.mapNatIso
      ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (equivSmallModel C).counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (equivSmallModel.{w} C).shrinkYonedaIsoConjugateYoneda.symm)).functor ⋙
    CostructuredArrow.pre ((equivSmallModel.{w} C).inverse) _ _
  have := isCardinalFiltered_costructuredArrow_yoneda (κ := κ)
    (P := ((equivSmallModel.{w} C).op.inverse ⋙ P))
      (by rwa [isCardinalContinuous_precomp_iff]) (fun J _ hJ ↦ by
      have := hC J hJ
      exact Adjunction.hasColimitsOfShape_of_equivalence (equivSmallModel.{w} C).inverse)
  exact IsCardinalFiltered.of_equivalence κ F.asEquivalence

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma exists_presentation_of_isCardinalContinuous
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C)
    {F : Cᵒᵖ ⥤ Type w}
    (hF : isCardinalContinuous _ _ κ F) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
      (G : J ⥤ C) (ι : G ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj F),
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  let e := equivSmallModel.{w} (CostructuredArrow shrinkYoneda.{w} F)
  refine ⟨SmallModel.{w} (CostructuredArrow shrinkYoneda.{w} F), inferInstance,
    ?_, e.inverse ⋙ CostructuredArrow.proj shrinkYoneda.{w} F,
    Functor.whiskerLeft e.inverse (CostructuredArrow.ι shrinkYoneda.{w} F),
    ⟨IsColimit.whiskerEquivalence (Presheaf.isColimitTautologicalCoconeShrink F ) e.symm⟩⟩
  have := isCardinalFiltered_costructuredArrow_shrinkYoneda hF hC
  exact IsCardinalFiltered.of_equivalence κ e

end EssentiallySmall

end Presheaf

end CategoryTheory
