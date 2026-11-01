/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Types.PreservesLimit
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.SmallRepresentatives

/-!
# `κ`-continuous functors

If `F : C ⥤ D` is a functor and `κ : Cardinal.{w}`, we say that
`F` is `κ`-continuous (`F.IsCardinalContinuous κ`) if it preserves
limits indexed by categories `J` such that `HasCardinalLT (Arrow J) κ`.
This defines a property of objects `isCardinalContinuous C D κ` in the
category of functors `C ⥤ D`. The corresponding fullsubcategory
is denoted `CardinalContinuousFunctor C D κ`.
We show that a functor is `ℵ₀`-continuous iff it preserves finite limits.

We show that if `C` is an essentially `w`-small category, then
`CardinalContinuousFunctor C (Type w) κ` is locally `κ`-presentable.
The proof reduces to the case of `CardinalContinuousFunctor Cᵒᵖ D κ`
where `C` is a `w`-small category, and this case is done by showing
that `κ`-continuous functors `Cᵒᵖ ⥤ Type w` are exactly the objects
that are local with respect to a suitable `w`-small family of morphisms,
see the lemma `Presheaf.isCardinalContinuous_eq_isLocal`.

If `C` is an essentially `w`-small category, we show that the category
`CardinalContinuousFunctor Cᵒᵖ (Type w) κ` contains representable
presheaves and is stable under `κ`-filtered colimits. If `κ`-small
colimits exists in `C`, we show that `κ`-continuous presheaves `Cᵒᵖ ⥤ Type w`
are exactly the `κ`-filtered colimits of representable presheaves,
see `Presheaf.exists_presentation_of_isCardinalContinuous`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite

namespace Functor

section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A functor `F : C ⥤ D` is `κ`-continuous if it preserves limits of shape `J`
where `J` is any small category such that `HasCardinalLT (Arrow J) κ` holds. -/
@[mk_iff]
class IsCardinalContinuous (F : C ⥤ D) (κ : Cardinal.{w}) : Prop where
  preservesLimitsOfShape (F) (κ) (J : Type w) [SmallCategory J]
    (hJ : HasCardinalLT (Arrow J) κ) : PreservesLimitsOfShape J F := by infer_instance

instance (F : C ⥤ D) [PreservesLimitsOfSize.{w, w} F] (κ : Cardinal.{w}) :
    F.IsCardinalContinuous κ where

instance (κ : Cardinal.{w}) {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCardinalContinuous κ] [G.IsCardinalContinuous κ] :
    (F ⋙ G).IsCardinalContinuous κ where
  preservesLimitsOfShape J _ hJ := by
    have := IsCardinalContinuous.preservesLimitsOfShape F κ J hJ
    have := IsCardinalContinuous.preservesLimitsOfShape G κ J hJ
    infer_instance

variable (C D) in
/-- Given a cardinal `κ`, this is the property of objects
in the category of functors `C ⥤ D` that is satisfied by `κ`-continuous
functors, i.e. functors which preserve limits indexed by categories `J`
such that `Arrow J` is of cardinality `< κ`. -/
abbrev isCardinalContinuous (κ : Cardinal.{w}) : ObjectProperty (C ⥤ D) :=
  fun F ↦ IsCardinalContinuous F κ

lemma isCardinalContinuous_eq_iInf (κ : Cardinal.{w}) :
  isCardinalContinuous C D κ =
    ⨅ (J : Type w) (_ : SmallCategory J) (_ : HasCardinalLT (Arrow J) κ),
      .preservesLimitsOfShape J := by
  ext
  simp [isCardinalContinuous_iff]

instance (κ : Cardinal.{w}) :
    (isCardinalContinuous C D κ).IsClosedUnderIsomorphisms := by
  rw [isCardinalContinuous_eq_iInf]
  infer_instance

lemma IsCardinalContinuous.of_iso {F G : C ⥤ D} (e : F ≅ G) (κ : Cardinal.{w})
    [F.IsCardinalContinuous κ] : G.IsCardinalContinuous κ :=
  (isCardinalContinuous C D κ).prop_of_iso e inferInstance

@[simp]
lemma isCardinalContinuous_precomp_iff {C' : Type u''} [Category.{v''} C']
    (G : C' ⥤ C) [G.IsEquivalence] (F : C ⥤ D) (κ : Cardinal.{w}) :
    (G ⋙ F).IsCardinalContinuous κ ↔ F.IsCardinalContinuous κ :=
  ⟨fun _ ↦ IsCardinalContinuous.of_iso
    (show G.inv ⋙ G ⋙ F ≅ F from (Functor.associator G.inv _ _ ).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso _ ≪≫ F.leftUnitor) κ,
    fun _ ↦ inferInstance⟩

@[simp]
lemma isCardinalContinuous_postcomp_iff {D' : Type u''} [Category.{v''} D']
    (F : C ⥤ D) (κ : Cardinal.{w}) (G : D ⥤ D') [G.IsEquivalence] :
    (F ⋙ G).IsCardinalContinuous κ ↔ F.IsCardinalContinuous κ :=
  ⟨fun _ ↦ IsCardinalContinuous.of_iso
    (show (F ⋙ G) ⋙ G.inv ≅ F from Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor) κ,
    fun _ ↦ inferInstance⟩

lemma isCardinalContinuous_eq_inverseImage_of_isEquivalence
    {C' : Type u''} [Category.{v''} C'] (G : C' ⥤ C) [G.IsEquivalence]
    (D : Type u') [Category.{v'} D] (κ : Cardinal.{w}) :
    isCardinalContinuous C D κ =
      (isCardinalContinuous C' D κ).inverseImage ((Functor.whiskeringLeft ..).obj G) := by
  aesop

lemma isCardinalContinuous_aleph0 :
    isCardinalContinuous C D .aleph0.{w} = .preservesFiniteLimits := by
  rw [isCardinalContinuous_eq_iInf, ObjectProperty.preservesFiniteLimits_eq_iInf]
  simp only [hasCardinalLT_aleph0_iff]
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    intro J _ _
    rw [ObjectProperty.congr_preservesLimitsOfShape C D (ULiftHomULiftCategory.equiv J)]
    exact (iInf_le _ (ULiftHom.{w} (ULift.{w} J))).trans ((iInf_le _ (by infer_instance)).trans
      ((iInf_le _ (by infer_instance)).trans (by rfl)))
  · simp only [le_iInf_iff]
    intro J _ _
    have := small_of_small_arrow.{0} J
    have := locallySmall_of_small_arrow.{0} J
    rw [ObjectProperty.congr_preservesLimitsOfShape C D
      ((Shrink.equivalence.{0} J).trans (ShrinkHoms.equivalence.{0} _))]
    refine (iInf_le _ (ShrinkHoms (Shrink.{0} J))).trans
      ((iInf_le _ (by infer_instance)).trans
      ((iInf_le _ (Nonempty.some ?_)).trans (by rfl)))
    rwa [← Arrow.finite_iff, ← hasCardinalLT_aleph0_iff.{0},
      hasCardinalLT_arrow_shrinkHoms_iff, hasCardinalLT_arrow_shrink_iff,
      hasCardinalLT_aleph0_iff.{0}]

@[simp]
lemma isCardinalContinuous_aleph0_iff_preservesFiniteLimits (F : C ⥤ D) :
    F.IsCardinalContinuous .aleph0.{w} ↔ PreservesFiniteLimits F := by
  rw [← ObjectProperty.preservesFiniteLimits, ← isCardinalContinuous_aleph0.{w}]

instance (F : C ⥤ D) [PreservesFiniteLimits F] :
    F.IsCardinalContinuous .aleph0.{w} := by
  simpa

end

end Functor

section

variable (C D : Type*) [Category* C] [Category* D] (κ : Cardinal.{w})

/-- The full subcategory of `C ⥤ D` consisting of `κ`-continuous functors, i.e.
functors which commute with limits of shape `J` where `J` is a small category
such that `HasCardinalLT (Arrow J) κ` holds. -/
abbrev CardinalContinuousFunctor : Type _ :=
    (Functor.isCardinalContinuous C D κ).FullSubcategory

/-- The full embedding `CardinalContinuousFunctor C D κ ⥤ C ⥤ D`. -/
abbrev CardinalContinuousFunctor.ι : CardinalContinuousFunctor C D κ ⥤ C ⥤ D :=
  ObjectProperty.ι _

instance {F : CardinalContinuousFunctor C D κ} : F.obj.IsCardinalContinuous κ := F.property

variable {C} in
/-- If two categories `C` and `C'` are equivalent, then the categories
of `κ`-continuous functors in `C ⥤ D` and `C' ⥤ D` are also equivalent. -/
@[implicit_reducible, simps!]
def CardinalContinuousFunctor.congrLeft {C' : Type*} [Category* C']
    (e : C ≌ C') (D : Type*) [Category* D] (κ : Cardinal.{w}) :
    CardinalContinuousFunctor C D κ ≌ CardinalContinuousFunctor C' D κ :=
  e.congrLeft.congrFullSubcategory (by aesop)

end

namespace Presheaf

open CategoryTheory.Functor

section Small

variable (C : Type w) [SmallCategory C] (κ : Cardinal.{w})

/-- Given a `w`-small category `C` and a cardinal `κ`, this is a
`w`-small family of morphisms in `Cᵒᵖ ⥤ Type w` such that `κ`-continuous
functors `Cᵒᵖ ⥤ Type w` are exactly the objects that are local with
respect to this family of morphisms, see the lemma `isCardinalContinuous_eq_isLocal`. -/
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
      exact IsCardinalContinuous.preservesLimitsOfShape P κ _
        (SmallCategoryCardinalLT.hasCardinalLT κ J)
    · simp only [isCardinalContinuous_eq_iInf, le_iInf_iff]
      intro J _ hJ
      obtain ⟨J', ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
      rw [← ObjectProperty.congr_preservesLimitsOfShape _ _ e]
      apply iInf_le
  · simp [preservesLimitsOfShape_eq_isLocal]

variable [Fact κ.IsRegular]

instance (J : SmallCategoryCardinalLT κ)
    (F : SmallCategoryCardinalLT.categoryFamily κ J ⥤ Cᵒᵖ)
    (X : (SmallCategoryCardinalLT.categoryFamily κ J)ᵒᵖ) :
    IsCardinalPresentable ((F.leftOp ⋙ shrinkYoneda.{w, w, w}).obj X) κ := by
  dsimp
  infer_instance

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

instance : (isCardinalContinuous Cᵒᵖ (Type w) κ).IsClosedUnderCardinalFilteredColimits κ := by
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isClosedUnderCardinalFilteredColimits_isLocal
  apply isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt

example : (CardinalContinuousFunctor.ι Cᵒᵖ (Type w) κ).IsCardinalAccessible κ := by
  infer_instance

instance : IsCardinalLocallyPresentable (CardinalContinuousFunctor Cᵒᵖ (Type w) κ) κ := by
  change IsCardinalLocallyPresentable
    (isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory κ
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isLocallyPresentable_isLocal
  apply isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt

instance : (CardinalContinuousFunctor.ι Cᵒᵖ (Type w) κ).IsRightAdjoint := by
  change (isCardinalContinuous Cᵒᵖ (Type w) κ).ι.IsRightAdjoint
  rw [isCardinalContinuous_eq_isLocal]
  apply MorphismProperty.isRightAdjoint_ι_isLocal _ κ
  apply isCardinalPresentable_isCardinalContinuousMorphismProperty_src_tgt

instance : HasLimitsOfSize.{w, w} (CardinalContinuousFunctor Cᵒᵖ (Type w) κ) := by
  change HasLimitsOfSize.{w, w} (isCardinalContinuous Cᵒᵖ (Type w) κ).FullSubcategory
  rw [isCardinalContinuous_eq_isLocal]
  exact ⟨inferInstance⟩

end Small

section EssentiallySmall

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular]

instance : (isCardinalContinuous C (Type w) κ).IsClosedUnderCardinalFilteredColimits κ := by
  rw [isCardinalContinuous_eq_inverseImage_of_isEquivalence
    ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans (opOpEquivalence C)).functor]
  infer_instance

instance : IsCardinalLocallyPresentable (CardinalContinuousFunctor C (Type w) κ) κ :=
  (CardinalContinuousFunctor.congrLeft ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans
    (opOpEquivalence C)) (Type w) κ).isCardinalLocallyPresentable κ

instance : IsLocallyPresentable.{w} (CardinalContinuousFunctor C (Type w) κ) where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

instance : (CardinalContinuousFunctor.ι C (Type w) κ).IsRightAdjoint := by
  let e := ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans (opOpEquivalence C))
  let e' := CardinalContinuousFunctor.congrLeft e (Type w) κ
  let iso : e'.inverse ⋙
      CardinalContinuousFunctor.ι (SmallModel.{w} Cᵒᵖ)ᵒᵖ (Type w) κ ⋙ e.congrLeft.functor ≅
      CardinalContinuousFunctor.ι C (Type w) κ :=
    isoWhiskerLeft e'.inverse (by exact Iso.refl _) ≪≫ (associator _ _ _).symm ≪≫
      isoWhiskerRight e'.counitIso _ ≪≫ leftUnitor _
  exact Functor.isRightAdjoint_of_iso iso

instance :
    HasLimitsOfSize.{w, w} (CardinalContinuousFunctor C (Type w) κ) :=
  Adjunction.has_limits_of_equivalence
    ((CardinalContinuousFunctor.congrLeft ((equivSmallModel.{w} Cᵒᵖ).op.symm.trans
      (opOpEquivalence C)) (Type w) κ).inverse)

omit [EssentiallySmall.{w} C] in
lemma isCardinalFiltered_elements_op
    (P : Cᵒᵖ ⥤ Type w) [P.IsCardinalContinuous κ]
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C) :
    IsCardinalFiltered P.Elementsᵒᵖ κ where
  nonempty_cocone {J _} F hJ := by
    have := hasLimitsOfShape_opposite_opposite_iff.mpr (hC J hJ)
    have := IsCardinalContinuous.preservesLimitsOfShape P κ Jᵒᵖ (by simpa)
    obtain ⟨f, hf⟩ := ((Types.isLimit_iff_bijective_sectionOfCone _).mp
      ⟨isLimitOfPreserves P (limit.isLimit (F.leftOp ⋙ Elements.π P))⟩).surjective
        { val j := (F.obj j.unop).unop.val
          property _ := by simp }
    replace hf (j : J) := congr($(hf).val (op j))
    dsimp at f hf
    exact ⟨op (elementsMk _ _ f),
      { app j := (Elements.homMk _ (hf j)).op
        naturality _ _ g := by
          ext
          simp [← limit.w (F.leftOp ⋙ Elements.π P) g.op] }⟩

variable (κ) in
lemma exists_presentation_of_isCardinalContinuous
    (hC : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      HasColimitsOfShape J C)
    (P : Cᵒᵖ ⥤ Type w) [P.IsCardinalContinuous κ] :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
      (G : J ⥤ C) (ι : G ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj P),
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  let e := equivSmallModel.{w} P.Elementsᵒᵖ
  have := isCardinalFiltered_elements_op P hC
  exact ⟨SmallModel.{w} P.Elementsᵒᵖ, inferInstance, IsCardinalFiltered.of_equivalence κ e, _,
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft e.inverse (Elements.shrinkYonedaCocone P).ι,
    ⟨(IsColimit.equivOfNatIsoOfIso (Functor.associator _ _ _) _ _
      (Cocone.ext (Iso.refl _))).symm
        (IsColimit.whiskerEquivalence (Elements.isColimitShrinkYonedaCocone P) e.symm)⟩⟩

end EssentiallySmall

end Presheaf

end CategoryTheory
