/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
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
    [∀ (Y : D), IsCardinalAccessibleCategory (StructuredArrow Y F) κ] :
    SolutionSetCondition.{w} F := by
  intro Y
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small.{w}
    (isCardinalPresentable (StructuredArrow Y F) κ)
  let ι := Shrink.{w} (Subtype P)
  let f (i : ι) : Subtype P := (equivShrink.{w} _).symm i
  have hf : Function.Surjective f := (equivShrink.{w} _).symm.surjective
  refine ⟨ι, fun i ↦ (f i).val.right, fun i ↦ (f i).val.hom,
    fun X g ↦ ?_⟩
  obtain ⟨Z, ⟨α⟩⟩ :
      ∃ (Z : Subtype P), Nonempty (Z.val ⟶ StructuredArrow.mk g) := by
    let E := (CostructuredArrow (isCardinalPresentable _ κ).ι ((StructuredArrow.mk g)))
    have : IsFiltered E := isFiltered_of_isCardinalFiltered _ κ
    let γ : E := Classical.arbitrary _
    obtain ⟨α, hα, ⟨e⟩⟩ := hP.le _ γ.left.property
    exact ⟨⟨α, hα⟩, ⟨e.inv ≫ γ.hom⟩⟩
  obtain ⟨i, rfl⟩ := hf Z
  exact ⟨i, α.right, StructuredArrow.w α⟩

end CategoryTheory
