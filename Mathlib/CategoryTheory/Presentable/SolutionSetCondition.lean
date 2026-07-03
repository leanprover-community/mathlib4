/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

/-!
# Accessible functor satisfy the solution set condition

-/

@[expose] public section

universe w

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

attribute [local instance] IsFiltered.nonempty in
lemma SolutionSetCondition.of_isCardinalAccessible
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F : C ⥤ D) [Functor.IsAccessible.{w} F] :
    SolutionSetCondition.{w} F := by
  intro Y
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} (StructuredArrow Y F)
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
