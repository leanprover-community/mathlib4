/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas

/-!
# The uniformization theorem

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT in
lemma Cardinal.SharplyLT.exists_retract_of_isCardinalPresentable
    {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    (hκ : κ₁.SharplyLT κ₂) {C : Type u} [Category.{v} C]
    [IsCardinalAccessibleCategory C κ₁] (X : C) [IsCardinalPresentable X κ₂] :
    ∃ (Y : C) (_ : Retract X Y) (J : Type w) (_ : PartialOrder J),
      IsCardinalFiltered J κ₁ ∧ HasCardinalLT J κ₂ ∧
        Nonempty ((isCardinalPresentable C κ₁).ColimitOfShape J Y) := by
  have hκ₁ := isCardinalFilteredGenerator_isCardinalPresentable C κ₁
  obtain ⟨J, _, _, ⟨p⟩⟩ :
      ∃ (J : Type w) (_ : PartialOrder J) (_ : IsCardinalFiltered J κ₁),
    Nonempty ((isCardinalPresentable C κ₁).ColimitOfShape J X) := by
      obtain ⟨J₀, _, _, ⟨p₀⟩⟩ := hκ₁.exists_colimitsOfShape X
      obtain ⟨J, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J₀ κ₁
      exact ⟨_, _, inferInstance, ⟨p₀.reindex F⟩⟩
  have : IsCardinalFiltered (Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) κ₂ :=
    isCardinalFiltered_subtype hκ.exists_isCardinalFiltered_set
  obtain ⟨K, i, hi⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ₂
    (isColimit κ₁ κ₂ p) (𝟙 X)
  exact ⟨colimit κ₁ κ₂ p K,
    { i := i, r := colimit.π κ₁ κ₂ p K }, Subtype K.val,
    inferInstance, K.prop.1, K.prop.2, ⟨.colimit _ (fun k ↦ p.prop_diag_obj _)⟩⟩

namespace CategoryTheory

open Limits

namespace IsCardinalAccessibleCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]


lemma uniformization'
    (F : C ⥤ D)
    {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    [IsCardinalAccessibleCategory C κ₁] [IsCardinalAccessibleCategory D κ₁]
    [F.IsCardinalAccessible κ₁] (hκ : κ₁.SharplyLT κ₂)
    (hF : isCardinalPresentable C κ₁ ≤ (isCardinalPresentable D κ₂).inverseImage F) :
    isCardinalPresentable C κ₂ ≤ (isCardinalPresentable D κ₂).inverseImage F := by
  intro X hX
  simp only [isCardinalPresentable_iff] at hX
  obtain ⟨Y, r, J, _, _, hJ, ⟨p⟩⟩ := hκ.exists_retract_of_isCardinalPresentable X
  refine (isCardinalPresentable D κ₂).prop_of_retract (r.map F) ?_
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ₁
  have (j : J) : IsCardinalPresentable ((p.diag ⋙ F).obj j) κ₂ := hF _ (p.prop_diag_obj j)
  exact isCardinalPresentable_of_isColimit _ (isColimitOfPreserves F p.isColimit) _
    ((hasCardinalLT_arrow_iff_of_isThin _ _ (Cardinal.IsRegular.aleph0_le Fact.out)).2 hJ)

lemma uniformization_of_small
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    {ι : Type*} [Small.{w} ι] (F : ι → C ⥤ D)
    [∀ i, Functor.IsAccessible.{w} (F i)] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory C κ ∧
      IsCardinalAccessibleCategory D κ ∧
      (∀ i, (F i).IsCardinalAccessible κ) ∧
        ∀ i, isCardinalPresentable C κ ≤ (isCardinalPresentable D κ).inverseImage (F i) := by
  obtain ⟨κ, _, _, _, _⟩ :
      ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
        IsCardinalAccessibleCategory C κ ∧ IsCardinalAccessibleCategory D κ ∧
          ∀ (i : ι), (F i).IsCardinalAccessible κ := by
    obtain ⟨κ₁, _, _⟩  := IsAccessibleCategory.exists_cardinal C
    obtain ⟨κ₂, _, _⟩  := IsAccessibleCategory.exists_cardinal D
    choose κ₃ _ hκ₃ using fun i ↦ Functor.IsAccessible.exists_cardinal (F i)
    obtain ⟨κ₃', hκ₃' , hκ₃''⟩ :=
      HasCardinalLT.exists_regular_cardinal_forall (fun i ↦ (κ₃ i).ord.ToType)
    have : Fact κ₃'.IsRegular := ⟨hκ₃'⟩
    obtain ⟨κ, _, hκ₁, hκ₂, hκ₃⟩ := Cardinal.SharplyLT.exists_of_triple κ₁ κ₂ κ₃'
    refine ⟨κ, inferInstance, hκ₁.isCardinalAccessibleCategory C,
      hκ₂.isCardinalAccessibleCategory D,
      fun i ↦ Functor.isCardinalAccessible_of_le _ (show κ₃ i ≤ κ from ?_)⟩
    have := (hκ₃'' i)
    simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] at this
    exact this.le.trans hκ₃.le
  obtain ⟨κ₀, _, hκ₀⟩ : ∃ (κ₀ : Cardinal.{w}) (_ : Fact κ₀.IsRegular),
      ∀ (i : ι), (isCardinalPresentable C κ).map (F i) ≤ isCardinalPresentable D κ₀ := by
    choose κ' hκ' hκ'' using
      fun i ↦ ObjectProperty.le_isCardinalPresentable.{w} ((isCardinalPresentable C κ).map (F i))
    obtain ⟨κ'', h₁, h₂⟩ :=
      HasCardinalLT.exists_regular_cardinal_forall (fun i ↦ (κ' i).ord.ToType)
    have : Fact κ''.IsRegular := ⟨h₁⟩
    refine ⟨κ'', inferInstance, fun i ↦ (hκ'' i).trans ?_⟩
    have := h₂ i
    simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] at this
    exact isCardinalPresentable_monotone _ this.le
  obtain ⟨κ', _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₀
  exact ⟨κ', inferInstance, h₁.isCardinalAccessibleCategory C,
    h₁.isCardinalAccessibleCategory D,
    fun i ↦ Functor.isCardinalAccessible_of_le _ h₁.le,
    fun i ↦ uniformization' _ h₁
      (fun X hX ↦ isCardinalPresentable_monotone _ h₂.le _
        (hκ₀ i _ (ObjectProperty.prop_map_obj _ _ hX)))⟩

lemma uniformization_pair (F₁ F₂ : C ⥤ D)
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    [Functor.IsAccessible.{w} F₁] [Functor.IsAccessible.{w} F₂] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory C κ ∧
      IsCardinalAccessibleCategory D κ ∧
      F₁.IsCardinalAccessible κ ∧ F₂.IsCardinalAccessible κ ∧
        isCardinalPresentable C κ ≤ (isCardinalPresentable D κ).inverseImage F₁ ∧
        isCardinalPresentable C κ ≤ (isCardinalPresentable D κ).inverseImage F₂ := by
  let F (i : Fin 2) : C ⥤ D := match i with | 0 => F₁ | 1 => F₂
  have (i : Fin 2) : Functor.IsAccessible.{w} (F i) := match i with
    | 0 => by assumption
    | 1 => by assumption
  obtain ⟨κ, _, h₁, h₂, h₃, h₄⟩ := uniformization_of_small F
  exact ⟨κ, inferInstance, h₁, h₂, h₃ 0, h₃ 1, h₄ 0, h₄ 1⟩

lemma uniformization (F : C ⥤ D)
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    [Functor.IsAccessible.{w} F] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory C κ ∧
      IsCardinalAccessibleCategory D κ ∧
      F.IsCardinalAccessible κ ∧
        isCardinalPresentable C κ ≤ (isCardinalPresentable D κ).inverseImage F := by
  obtain ⟨κ, _, h₁, h₂, h₃, h₄⟩ := uniformization_of_small (fun (_ : Fin 1) ↦ F)
  exact ⟨κ, inferInstance, h₁, h₂, h₃ 0, h₄ 0⟩

end IsCardinalAccessibleCategory

end CategoryTheory
