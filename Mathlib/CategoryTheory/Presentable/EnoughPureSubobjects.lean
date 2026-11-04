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

universe w

namespace CategoryTheory

variable {C : Type*} [Category* C]

open Limits

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
      P.IsClosedUnderCardinalPureSubobjects κ' := by
  obtain ⟨κ', _, h, _, _⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      P.ι.PreservesCardinalPresentable κ' ∧
        IsCardinalAccessibleCategory.{w} P.FullSubcategory κ' := by
    have := P.isAccessible_ι κ
    obtain ⟨κ₁, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization P.ι
    obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
    exact ⟨κ₂, inferInstance, h, h₁.preservesCardinalPresentable _,
      h₁.isCardinalAccessibleCategory _⟩
  have : P.IsClosedUnderCardinalFilteredColimits κ' := .of_le h.le
  exact ⟨κ', inferInstance, h, inferInstance⟩

end ObjectProperty

namespace IsCardinalAccessibleCategory

-- 2.33
variable (C) in
lemma test (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (h : κ.SharplyLT κ'),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : IsCardinalPresentable X κ'),
        ∃ (X' : C) (_ : IsCardinalPresentable X' κ') (f' : X ⟶ X') (i : X' ⟶ Y)
          (_ : Mono i) (_ : IsCardinalPure κ i), f' ≫ i = f := sorry

variable (C) in
lemma test' (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ]
    (α : Cardinal.{w}) [Fact α.IsRegular] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ') (_ : α ≤ κ'),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : IsCardinalPresentable X κ'),
        ∃ (X' : C) (_ : IsCardinalPresentable X' κ') (f' : X ⟶ X') (i : X' ⟶ Y)
          (_ : Mono i) (_ : IsCardinalPure κ i), f' ≫ i = f := by
  obtain ⟨β, _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ α
  have := h₁.isCardinalAccessibleCategory C
  obtain ⟨κ', _, h₃, h⟩ := test C β
  refine ⟨κ', inferInstance, h₁.trans h₃, h₂.le.trans h₃.le,
    fun _ _ f _ ↦ ?_⟩
  obtain ⟨X', _, f', i, hf', _, fac⟩ := h f inferInstance
  exact ⟨X', inferInstance, f', i, inferInstance, .of_le h₁.le _, fac⟩

end IsCardinalAccessibleCategory

end CategoryTheory
