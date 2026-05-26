/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.SharplyLT

/-!
# The uniformization theorem

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory in
lemma Cardinal.SharplyLT.exists_retract_of_isCardinalPresentable
    {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
    (hκ : κ₁.SharplyLT κ₂) {C : Type u} [Category.{v} C]
    [IsCardinalAccessibleCategory C κ₁] (X : C) [IsCardinalPresentable X κ₂] :
    ∃ (Y : C) (r : Retract X Y) (J : Type w) (_ : PartialOrder J),
      IsCardinalFiltered J κ₁ ∧ HasCardinalLT J κ₂ ∧
        Nonempty ((isCardinalPresentable C κ₁).ColimitOfShape J Y) := by
  sorry

namespace CategoryTheory

open Limits

namespace IsCardinalAccessibleCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]
  [IsCardinalAccessibleCategory C κ₁] [IsCardinalAccessibleCategory D κ₁]
  [F.IsCardinalAccessible κ₁] (hκ : κ₁.SharplyLT κ₂)

include hκ in
lemma uniformization
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

end IsCardinalAccessibleCategory

end CategoryTheory
