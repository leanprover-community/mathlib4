/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

/-!
# Accessible functors satisfy the solution set condition

If `F : C ⥤ D` is an accessible functor between accessible categories,
then `F` satisfies the solution set condition (this is corollary 2.45 in
the book by Adámek and Rosický).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- An accessible functor between accessible categories satisfies the solution set condition.
This is corollary 2.45 in [Adamek_Rosicky_1994]. -/
lemma SolutionSetCondition.of_isCardinalAccessible
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D]
    (F : C ⥤ D) [Functor.IsAccessible.{w} F] :
    SolutionSetCondition.{w} F := by
  intro Y
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} (StructuredArrow Y F)
  obtain ⟨ι, X₀, h⟩ := ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj.{w}
    (isCardinalPresentable (StructuredArrow Y F) κ)
  refine ⟨ι, fun i ↦ (X₀ i).right, fun i ↦ (X₀ i).hom, fun X g ↦ ?_⟩
  let E := CostructuredArrow (isCardinalPresentable _ κ).ι (StructuredArrow.mk g)
  have : IsFiltered E := isFiltered_of_isCardinalFiltered _ κ
  have : Nonempty E := IsFiltered.nonempty
  let γ : E := Classical.arbitrary _
  obtain ⟨_, ⟨i⟩, ⟨e⟩⟩ := h.le _ γ.left.property
  exact ⟨i, _, StructuredArrow.w (e.inv ≫ γ.hom)⟩

end CategoryTheory
