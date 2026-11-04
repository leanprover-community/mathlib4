/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalPure
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Representation
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Presentable.Uniformization

/-!
# ...

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v₁ v₂

namespace CategoryTheory

variable {C : Type*} [Category* C]

instance {P : ObjectProperty C} (X : P.FullSubcategory) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] [P.ι.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X.obj κ :=
  inferInstanceAs (IsCardinalPresentable (P.ι.obj X) κ)

lemma IsCardinalPure.of_full_of_faithful
    {κ : Cardinal.{w}} [Fact κ.IsRegular] {X Y : C} {f : X ⟶ Y}
    {D : Type*} [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesCardinalPresentable κ]
    (h : IsCardinalPure κ (F.map f) := by infer_instance) :
    IsCardinalPure κ f where
  exists_of_commSq sq := by
    obtain ⟨ρ, hρ⟩ := exists_of_commSq κ (sq.map F)
    exact ⟨F.preimage ρ, F.map_injective (by cat_disch)⟩


open Limits

-- to be moved
section

open Opposite

lemma isCardinalPresentable_iff_isAccessible_shrinkCoyoneda [LocallySmall.{w} C]
    {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular] :
    IsCardinalPresentable X κ ↔ (shrinkCoyoneda.{w}.obj (op X)).IsCardinalAccessible κ := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun J _ _ ↦ ?_⟩⟩
  have := (shrinkCoyoneda.{w}.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := preservesColimitsOfShape_of_natIso (J := J) (shrinkCoyonedaObjCompUliftFunctorIso (op X))
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor

lemma IsCardinalPresentable.of_full_of_faithful
    {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular] {D : Type*} [Category* D]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.IsCardinalAccessible κ]
    (h : IsCardinalPresentable (F.obj X) κ := by infer_instance) :
    IsCardinalPresentable X κ := by
  rw [isCardinalPresentable_iff_isAccessible_shrinkCoyoneda.{w}] at h ⊢
  have : (F ⋙ shrinkCoyoneda.{w}.obj (F.op.obj (op X))).IsCardinalAccessible κ := by
    dsimp
    infer_instance
  exact Functor.isCardinalAccessible_of_natIso (asIso (shrinkCoyonedaMap F (op X))).symm _

end

namespace ObjectProperty

class IsClosedUnderCardinalPureSubobjects
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  prop_of_isCardinalPure (P κ) {X Y : C} (f : X ⟶ Y) [IsCardinalPure κ f] (hY : P Y) : P X

export IsClosedUnderCardinalPureSubobjects (prop_of_isCardinalPure)

lemma IsClosedUnderCardinalPureSubobjects.isClosedUnderIsomorphisms
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalPureSubobjects κ] :
    P.IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_isCardinalPure κ e.inv h

lemma IsClosedUnderCardinalPureSubobjects.of_le {P : ObjectProperty C} {κ κ' : Cardinal.{w}}
    [Fact κ.IsRegular] [Fact κ'.IsRegular] (h : κ ≤ κ')
    [P.IsClosedUnderCardinalPureSubobjects κ] :
    P.IsClosedUnderCardinalPureSubobjects κ' where
  prop_of_isCardinalPure f _ hY := by
    have : IsCardinalPure κ f := .of_le h f
    exact P.prop_of_isCardinalPure κ f hY


end ObjectProperty

namespace IsCardinalAccessibleCategory

open ObjectProperty.IsClosedUnderCardinalFilteredColimits in
instance [EssentiallySmall.{w} C] (P : ObjectProperty (C ⥤ Type w))
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [IsCardinalAccessibleCategory P.FullSubcategory κ]
    [P.ι.PreservesCardinalPresentable κ] :
    P.IsClosedUnderCardinalPureSubobjects κ where
  prop_of_isCardinalPure {F₁ F₂} f _ hF₂ := by
    let J := CostructuredArrow (isCardinalPresentable (C ⥤ Type w) κ).ι F₁
    let D : J ⥤ C ⥤ Type w :=
      CostructuredArrow.proj _ F₁ ⋙ (isCardinalPresentable (C ⥤ Type w) κ).ι
    let c : Cocone D := (Functor.LeftExtension.mk _ (Functor.rightUnitor _).inv).coconeAt F₁
    have hc : IsColimit c := (isCardinalPresentable _ κ).ι.denseAt F₁
    let D' : (P.inverseImage D).FullSubcategory ⥤ P.FullSubcategory :=
      P.lift (ObjectProperty.ι _ ⋙ D) (fun ⟨_, _⟩ ↦ by simpa)
    let e : D' ⋙ P.ι ≅ ObjectProperty.ι _ ⋙ D := Iso.refl _
    have := isFiltered_of_isCardinalFiltered J κ
    have : (P.inverseImage D).ι.Final := by
      rw [ObjectProperty.final_ι_iff_of_isFiltered]
      intro j
      have : IsCardinalPresentable (D.obj j) κ := by dsimp [D]; infer_instance
      let J' := CostructuredArrow (isCardinalPresentable P.FullSubcategory κ).ι ⟨F₂, hF₂⟩
      have := isCardinalClosedUnderColimitsOfShape P κ J'
      have : HasColimitsOfShape J' (Type w) :=
        hasColimitsOfShape_of_equivalence (equivSmallModel.{w} J').symm
      obtain ⟨Z, z, hz⟩ :=
        IsCardinalPresentable.exists_hom_of_isColimit κ (isColimitOfPreserves P.ι
          ((isCardinalPresentable P.FullSubcategory κ).ι.denseAt ⟨F₂, hF₂⟩)) (c.ι.app j ≫ f)
      have : IsCardinalPresentable Z.left.obj.obj κ :=
        inferInstanceAs (IsCardinalPresentable (P.ι.obj Z.left.obj) κ)
      dsimp at z hz
      rw [Category.id_comp] at hz
      obtain ⟨r, hr⟩ := IsCardinalPure.exists_of_commSq κ ⟨hz⟩
      exact ⟨CostructuredArrow.mk (Y := ⟨Z.left.obj.obj, inferInstance⟩) (by exact r),
        by exact Z.left.obj.property, ⟨CostructuredArrow.homMk (ObjectProperty.homMk (by exact z))⟩⟩
    have : IsCardinalFiltered (P.inverseImage D).FullSubcategory κ :=
      ObjectProperty.isCardinalFiltered ..
    have := isCardinalClosedUnderColimitsOfShape P κ (P.inverseImage D).FullSubcategory
    exact P.prop_of_isColimit
      ((IsColimit.precomposeHomEquiv e _).symm
        ((Functor.Final.isColimitWhiskerEquiv (P.inverseImage D).ι _).symm hc))
      (fun X ↦ (D'.obj X).property)

end IsCardinalAccessibleCategory

namespace ObjectProperty

-- to be moved
lemma isAccessible_ι (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ] [IsAccessibleCategory.{w} C] :
    Functor.IsAccessible.{w} P.ι := by
  obtain ⟨κ₁, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
  have := h₁.isCardinalAccessibleCategory C
  have : P.IsClosedUnderCardinalFilteredColimits κ₂ := .of_le h.le
  refine ⟨κ₂, inferInstance, ?_⟩
  infer_instance

-- key part of Proposition 2.32
lemma isClosedUnderCardinalPureSubobjects
    [EssentiallySmall.{w} C] (P : ObjectProperty (C ⥤ Type w))
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [IsAccessibleCategory.{w} P.FullSubcategory] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      P.IsClosedUnderCardinalPureSubobjects κ' ∧
      IsCardinalAccessibleCategory P.FullSubcategory κ' ∧
      P.ι.IsCardinalAccessible κ' ∧
        P.ι.PreservesCardinalPresentable κ' := by
  obtain ⟨κ', _, h, _, _⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      P.ι.PreservesCardinalPresentable κ' ∧
        IsCardinalAccessibleCategory.{w} P.FullSubcategory κ' := by
    have := P.isAccessible_ι κ
    obtain ⟨κ₁, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization P.ι
    obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
    exact ⟨κ₂, inferInstance, h, h₁.preservesCardinalPresentable _,
      h₁.isCardinalAccessibleCategory _⟩
  have : P.IsClosedUnderCardinalFilteredColimits κ' := .of_le h.le
  exact ⟨κ', inferInstance, h, inferInstance, inferInstance, inferInstance, inferInstance⟩

end ObjectProperty

class HasEnoughPureSubobjects (C : Type*) [Category* C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop
    extends IsCardinalAccessibleCategory C κ where
  exists_isCardinalPure (κ) {X Y : C} (f : X ⟶ Y) [IsCardinalPresentable X κ] :
    ∃ (X' : C) (_ : IsCardinalPresentable X' κ) (f' : X ⟶ X') (i : X' ⟶ Y),
      IsCardinalPure κ i ∧ f' ≫ i = f

lemma HasEnoughPureSubobjects.of_equivalence {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (_ : HasEnoughPureSubobjects C κ := by infer_instance) :
    HasEnoughPureSubobjects D κ where
  toIsCardinalAccessibleCategory := e.isCardinalAccessibleCategory _
  exists_isCardinalPure {X Y} f _ := by
    obtain ⟨X', _, f', i, _, fac⟩ := exists_isCardinalPure κ (e.inverse.map f)
    refine ⟨e.functor.obj X', inferInstance, e.symm.toAdjunction.homEquiv _ _ f',
      (e.toAdjunction.homEquiv _ _).symm i, ?_,
      e.inverse.map_injective
        (by simpa [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply])⟩
    simp only [Adjunction.homEquiv_symm_apply, Equivalence.toAdjunction_counit]
    infer_instance

namespace IsCardinalAccessibleCategory

open HasEnoughPureSubobjects

lemma step₁ (C : Type w) [SmallCategory C] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (h : κ.SharplyLT κ'),
      HasEnoughPureSubobjects (C ⥤ Type w) κ' := by
  sorry

lemma step₂ {C : Type*} [Category* C] (P : ObjectProperty C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory P.FullSubcategory κ]
    [P.ι.PreservesCardinalPresentable κ]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [P.IsClosedUnderCardinalPureSubobjects κ]
    [HasEnoughPureSubobjects C κ] :
    HasEnoughPureSubobjects P.FullSubcategory κ where
  exists_isCardinalPure {X Y} f _ := by
    obtain ⟨X', _, f', i, _, fac⟩ := exists_isCardinalPure κ f.hom
    exact ⟨⟨X', P.prop_of_isCardinalPure κ i Y.property⟩,
      .of_full_of_faithful P.ι (by assumption),
      ObjectProperty.homMk f', ObjectProperty.homMk i,
      IsCardinalPure.of_full_of_faithful P.ι (by assumption), by cat_disch⟩

attribute [instance] step₂

lemma hasEnoughPureSubobjects (C : Type*) [Category* C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      HasEnoughPureSubobjects C κ' := by
  obtain ⟨A, _, P, _, _, ⟨e⟩⟩ :=
    IsCardinalAccessibleCategory.exists_equivalence_fullSubcategory C κ
  have : IsAccessibleCategory.{w} P.FullSubcategory := ⟨κ, inferInstance, inferInstance⟩
  obtain ⟨κ₁, _, h₁, _, _, _, _⟩ := P.isClosedUnderCardinalPureSubobjects κ
  obtain ⟨κ₂, inferInstance, h₂, _⟩ := step₁ A κ₁
  have := h₂.preservesCardinalPresentable P.ι
  have := h₂.isCardinalAccessibleCategory P.FullSubcategory
  have : P.IsClosedUnderCardinalFilteredColimits κ₂ := .of_le (h₁.trans h₂).le
  have : P.IsClosedUnderCardinalPureSubobjects κ₂ := .of_le h₂.le
  exact ⟨κ₂, inferInstance, h₁.trans h₂,
    HasEnoughPureSubobjects.of_equivalence e.symm _⟩

end IsCardinalAccessibleCategory

namespace IsAccessibleCategory

lemma hasEnoughPureSubobjects (C : Type*) [Category* C]
    [IsAccessibleCategory.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      HasEnoughPureSubobjects C κ' := by
  obtain ⟨κ₁, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
  have := h₁.isCardinalAccessibleCategory C
  obtain ⟨κ', _, h', _⟩ := IsCardinalAccessibleCategory.hasEnoughPureSubobjects C κ₂
  exact ⟨κ', inferInstance, h.trans h', inferInstance⟩

end IsAccessibleCategory

end CategoryTheory
