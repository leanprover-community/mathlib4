/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated

/-!
# The truncation of a quasicategory

In this file, we show that if `X : SSet` is a quasicategory, then
`((truncation 2).obj X)` satisfies the property `SSet.Truncated.Quasicategory₂`.

-/

@[expose] public section

universe u

open Simplicial CategoryTheory

namespace SSet

instance (X : SSet.{u}) [X.Quasicategory] :
    ((truncation 2).obj X).Quasicategory₂ where
  fill21 {x₀ : X _⦋0⦌} {x₁ : X _⦋0⦌} {x₂ : X _⦋0⦌} (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) := by
    change Nonempty ((e₀₂ : Edge x₀ x₂) × Edge.CompStruct e₀₁ e₁₂ e₀₂)
    obtain ⟨σ, hσ₁, hσ₂⟩ :=
      horn₂₁.isPushout.exists_desc (yonedaEquiv.symm e₀₁.edge)
        (yonedaEquiv.symm e₁₂.edge) (by simp)
    obtain ⟨s, hs⟩ := Quasicategory.hornFilling (by simp) (by simp) σ
    have hs₀ : stdSimplex.δ 0 ≫ s = yonedaEquiv.symm e₁₂.edge := by
      simp [← hσ₂, hs]
    have hs₂ : stdSimplex.δ 2 ≫ s = yonedaEquiv.symm e₀₁.edge := by
      simp [← hσ₁, hs]
    obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective s
    refine ⟨Edge.mk (X.δ 1 s) (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_),
      Edge.CompStruct.mk s
        (yonedaEquiv.symm.injective (by simp [← hs₂, stdSimplex.δ_comp_yonedaEquiv_symm]))
        (yonedaEquiv.symm.injective (by simp [← hs₀, stdSimplex.δ_comp_yonedaEquiv_symm]))⟩
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_self_assoc (i := 1), hs₂]
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 0) (by simp), hs₀]
  fill31 {x₀ : X _⦋0⦌} {x₁ : X _⦋0⦌} {x₂ : X _⦋0⦌} {x₃ : X _⦋0⦌}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₂₃ : Edge x₂ x₃) (e₀₂ : Edge x₀ x₂)
      (e₁₃ : Edge x₁ x₃) (e₀₃ : Edge x₀ x₃)
      (f₃ : Edge.CompStruct e₀₁ e₁₂ e₀₂) (f₀ : Edge.CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : Edge.CompStruct e₀₁ e₁₃ e₀₃) := by
    change Nonempty (Edge.CompStruct e₀₂ e₂₃ e₀₃)
    obtain ⟨σ, hσ₀, hσ₂, hσ₃⟩ := horn₃₁.exists_desc (yonedaEquiv.symm f₀.simplex)
      (yonedaEquiv.symm f₂.simplex) (yonedaEquiv.symm f₃.simplex) (by simp) (by simp) (by simp)
    obtain ⟨s, hs⟩ := Quasicategory.hornFilling (by simp) (by simp) σ
    have hs₀ : stdSimplex.δ 0 ≫ s = yonedaEquiv.symm f₀.simplex := by simp [← hσ₀, hs]
    have hs₂ : stdSimplex.δ 2 ≫ s = yonedaEquiv.symm f₂.simplex := by simp [← hσ₂, hs]
    have hs₃ : stdSimplex.δ 3 ≫ s = yonedaEquiv.symm f₃.simplex := by simp [← hσ₃, hs]
    obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective s
    refine ⟨Edge.CompStruct.mk (X.δ 1 s) (yonedaEquiv.symm.injective ?_)
      (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_)⟩
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        ← dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 1) (j := 2) (by simp), hs₃]
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 0) (j := 0) (by simp), hs₀]
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_self_assoc (i := 1), hs₂]
  fill32 {x₀ : X _⦋0⦌} {x₁ : X _⦋0⦌} {x₂ : X _⦋0⦌} {x₃ : X _⦋0⦌}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₂₃ : Edge x₂ x₃) (e₀₂ : Edge x₀ x₂)
      (e₁₃ : Edge x₁ x₃) (e₀₃ : Edge x₀ x₃)
      (f₃ : Edge.CompStruct e₀₁ e₁₂ e₀₂) (f₀ : Edge.CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : Edge.CompStruct e₀₂ e₂₃ e₀₃) := by
    change Nonempty (Edge.CompStruct e₀₁ e₁₃ e₀₃)
    obtain ⟨σ, hσ₀, hσ₁, hσ₃⟩ := horn₃₂.exists_desc (yonedaEquiv.symm f₀.simplex)
      (yonedaEquiv.symm f₁.simplex) (yonedaEquiv.symm f₃.simplex) (by simp) (by simp) (by simp)
    obtain ⟨s, hs⟩ := Quasicategory.hornFilling (by simp) (by simp) σ
    have hs₀ : stdSimplex.δ 0 ≫ s = yonedaEquiv.symm f₀.simplex := by simp [← hσ₀, hs]
    have hs₁ : stdSimplex.δ 1 ≫ s = yonedaEquiv.symm f₁.simplex := by simp [← hσ₁, hs]
    have hs₃ : stdSimplex.δ 3 ≫ s = yonedaEquiv.symm f₃.simplex := by simp [← hσ₃, hs]
    obtain ⟨s, rfl⟩ := yonedaEquiv.symm.surjective s
    refine ⟨Edge.CompStruct.mk (X.δ 2 s) (yonedaEquiv.symm.injective ?_)
      (yonedaEquiv.symm.injective ?_) (yonedaEquiv.symm.injective ?_)⟩
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_self_assoc (n := 1) (i := 2), hs₃]
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 0) (j := 1) (by simp), hs₀]
    · simp [← stdSimplex.δ_comp_yonedaEquiv_symm,
        dsimp% stdSimplex.δ_comp_δ_assoc (n := 1) (i := 1) (j := 1) (by simp), hs₁]

end SSet
