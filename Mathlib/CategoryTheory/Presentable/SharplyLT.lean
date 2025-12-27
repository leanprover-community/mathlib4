/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset

/-!
# Sharply smaller regular cardinals

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace Cardinal

variable {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]

variable (κ₁ κ₂) in
structure SharplyLT : Prop where
  lt : κ₁ < κ₂
  isCardinalAccessible_cardinalDirectedPoset :
    IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂

namespace SharplyLT

lemma le (h : SharplyLT κ₁ κ₂) : κ₁ ≤ κ₂ := h.lt.le

section

/-- Whan `k₁` is sharply smaller than `κ₂`, and `C` is a `κ₁`-accessible category, this
is a property of objects which allows to show that `C` is a `κ₂`-accessible category.
This property is defined as the closure of `κ₁`-presentable objects under
colimits of shape `J` for categories `J` such that `Arrow J` is of cardinality `< κ₂`. -/
def generator (_ : SharplyLT κ₁ κ₂) (C : Type u) [Category.{v} C] :
    ObjectProperty C :=
  (isCardinalPresentable C κ₁).colimitsCardinalClosure κ₂

variable (h : SharplyLT κ₁ κ₂) (C : Type u) [Category.{v} C]

lemma generator_le_sCardinalPresentable [LocallySmall.{w} C] :
    h.generator C ≤ isCardinalPresentable C κ₂ :=
  ObjectProperty.colimitsCardinalClosure_le _ _
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ)
    (isCardinalPresentable_monotone _ h.le)

instance [IsCardinalAccessibleCategory C κ₁] :
    ObjectProperty.EssentiallySmall.{w} (h.generator C) := by
  dsimp [generator]
  infer_instance

variable [IsCardinalAccessibleCategory C κ₁]

namespace isCardinalFilteredGenerator

def prop (_ : SharplyLT κ₁ κ₂) (J : Type w) [PartialOrder J] (A : Set J) : Prop :=
  IsCardinalFiltered (Subtype A) κ₁ ∧ HasCardinalLT (Subtype A) κ₂

variable {C} {X : C} {J : Type w} [PartialOrder J] [IsCardinalFiltered J κ₁]
  (p : (isCardinalPresentable C κ₁).ColimitOfShape J X)

instance (A : Subtype (prop h J)) :
    HasColimit ((Subtype.mono_coe A.val).functor ⋙ p.diag) := by
  have := A.prop.1
  infer_instance

variable {h} in
noncomputable def colimit (A : Subtype (prop h J)) : C :=
    Limits.colimit ((Subtype.mono_coe A.val).functor ⋙ p.diag)

noncomputable def functor : Subtype (prop h J) ⥤ C where
  obj A := colimit p A
  map {A₁ A₂} f := by
    sorry
  map_id := sorry
  map_comp := sorry

end isCardinalFilteredGenerator

lemma isCardinalFilteredGenerator :
    (h.generator C).IsCardinalFilteredGenerator κ₂ where
  le_isCardinalPresentable := h.generator_le_sCardinalPresentable C
  exists_colimitsOfShape X := by
    sorry

end

lemma isCardinalAccessible (h : SharplyLT κ₁ κ₂)
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ where
  toHasCardinalFilteredColimits := .of_le C h.le
  exists_generator :=
    ⟨_, inferInstance, h.isCardinalFilteredGenerator C⟩

lemma trans (h₁₂ : SharplyLT κ₁ κ₂) {κ₃ : Cardinal.{w}} [Fact κ₃.IsRegular]
    (h₂₃ : SharplyLT κ₂ κ₃) :
    SharplyLT κ₁ κ₃ where
  lt := h₁₂.lt.trans h₂₃.lt
  isCardinalAccessible_cardinalDirectedPoset := by
    have := h₁₂.isCardinalAccessible_cardinalDirectedPoset
    exact h₂₃.isCardinalAccessible _

end SharplyLT

end Cardinal
