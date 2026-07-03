/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

/-!
# Accessible functor satisfy the solution set condition

-/

@[expose] public section

universe w

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

-- when the uniformization theorem and the accessibility of comma categories
-- enters mathlib, the assumption can be changed
attribute [local instance] IsFiltered.nonempty in
lemma SolutionSetCondition.of_isCardinalAccessible
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ (Y : D), IsCardinalAccessibleCategory.{w} (StructuredArrow Y F) κ] :
    SolutionSetCondition.{w} F := by
  intro Y
  obtain ⟨ι, X₀, h⟩ := ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj.{w}
    (isCardinalPresentable (StructuredArrow Y F) κ)
  refine ⟨ι, fun i ↦ (X₀ i).right, fun i ↦ (X₀ i).hom,
    fun X g ↦ ?_⟩
  let E := CostructuredArrow (isCardinalPresentable _ κ).ι (StructuredArrow.mk g)
  have : IsFiltered E := isFiltered_of_isCardinalFiltered _ κ
  let γ : E := Classical.arbitrary _
  obtain ⟨_, ⟨i⟩, ⟨e⟩⟩ := h.le _ γ.left.property
  exact ⟨i, _, StructuredArrow.w (e.inv ≫ γ.hom)⟩

end CategoryTheory
