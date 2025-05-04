/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L2Space

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semi-definiteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.Gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → α` for an
`InnerProductSpace 𝕜 α`.
* `Matrix.L2Gram` : special case of `Matrix.Gram` where the `InnerProductSpace 𝕜 α`
  is an `L2`-space.

## Main results

* `Matrix.Gram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix MeasureTheory

open scoped InnerProductSpace

variable {E n : Type*}
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def Gram (𝕜 : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : n → E) : Matrix n n 𝕜  := fun i j ↦ inner 𝕜 (v i) (v j)

local notation "⟪" x ", " y "⟫" => @inner 𝕜  _ _ x y

/-- A `M : Matrix n n 𝕜` is a Gram matrix if `M = Gram 𝕜 v` for some `v : n → E`. -/
def IsGram (M : Matrix n n 𝕜) (v : n → E) : Prop := (M = Gram 𝕜 v)

namespace IsGram

@[simp]
lemma of_Gram (v : n → E) : IsGram (Gram 𝕜 v) v := by
  rfl

/-- For `M : Matrix n n 𝕜` with `IsGram M v`, the entry at `i j : n` equals `⟪v i, v j⟫`. -/
lemma entry {M : Matrix n n 𝕜} {v : n → E} (hM : IsGram M v) (i j : n) : M i j = ⟪v i, v j⟫ := by
  rw [hM, Gram]

/-- A Gram matrix is Hermitian. -/
lemma IsHermitian {M : Matrix n n 𝕜} {v : n → E} (hM : IsGram M v) : M.IsHermitian := by
  refine IsHermitian.ext_iff.mpr (fun i j ↦ ?_)
  rw [hM, Gram, Gram]
  simp only [RCLike.star_def, inner_conj_symm]

/-- A Gram matrix is positive semidefinite. -/
theorem PosSemidef [Fintype n] {M : Matrix n n 𝕜} {v : n → E} (hM : IsGram M v) :
    @PosSemidef _ _ _ _ toPartialOrder _ M := by
  refine ⟨hM.IsHermitian, fun x ↦ ?_⟩
  let y := ∑ (i : n), x i • v i
  have h : ⟪y, y⟫ = star x ⬝ᵥ M *ᵥ x := by
    simp [y]
    calc
      ⟪y, y⟫ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ⟪v i, v j⟫) := by
          simp_rw [y, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
        _ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * (M i j)) := by
          simp_rw [hM.entry]
        _ = star x ⬝ᵥ M *ᵥ x := by
          simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct,
            mul_comm, ← star_def]
          rfl
  rw [← h, le_iff_re_im]
  refine ⟨?_, ?_⟩
  · simp only [map_zero]
    exact inner_self_nonneg
  · simp only [map_zero, inner_self_im, y]

end IsGram

end Matrix

section L2

open L2 ENNReal

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Special case of a Gram matrix where the underlying inner product space is an L2-space. -/
noncomputable def Matrix.L2Gram (v : n → (α →₂[μ] 𝕜)) :
  Matrix n n 𝕜 := Gram 𝕜 v

lemma Matrix.IsGram.of_L2Gram (v : n →  (α →₂[μ] 𝕜)) : IsGram (L2Gram v) v := by
  rfl

lemma innerProduct_eq_inter (v w : (Set α)) (hv₁ : MeasurableSet v)
  (hw₁ : MeasurableSet w) (hv₂ : μ v ≠ ⊤) (hw₂ : μ w ≠ ⊤) :
  ⟪((indicatorConstLp 2 hv₁ hv₂ (1 : ℝ))), (indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) ⟫ =
    (μ (v ∩ w)).toReal := by
  rw [inner_indicatorConstLp_one]
  have h : ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) =ᶠ[ae μ] w.indicator fun x ↦ (1 : ℝ) :=
    indicatorConstLp_coeFn (hs := hw₁) (hμs := hw₂)
  have g : ∀ᵐ (x : α) ∂μ, x ∈ v → ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) x =
      w.indicator (fun x ↦ (1 : ℝ)) x := Filter.Eventually.mono h fun x a a_1 ↦ a
  rw [setIntegral_congr_ae hv₁ g, setIntegral_indicator hw₁]
  simp
  rfl

/-- A matrix with entry `μ (v i ∩ v j)` at index `i j : n`. -/
def interMatrix (μ : Measure α) (v : n → (Set α)) : Matrix n n ℝ := fun i j ↦ (μ (v i ∩ v j)).toReal

theorem posSemidef_interMatrix [Fintype n] (μ : Measure α) (v : n → (Set α))
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ⊤) :
      PosSemidef (interMatrix μ v) := by
  let M : Matrix n n ℝ := Matrix.L2Gram fun i ↦ (indicatorConstLp 2 (hv₁ i) (hv₂ i) (1 : ℝ))
  obtain hg := Matrix.IsGram.of_L2Gram fun i ↦ (indicatorConstLp 2 (hv₁ i) (hv₂ i) (1 : ℝ))
  have hf : (fun i j ↦ (μ (v i ∩ v j)).toReal) =
    (fun i j ↦ ⟪(indicatorConstLp 2 (hv₁ i) (hv₂ i) (1 : ℝ)),
    (indicatorConstLp 2 (hv₁ j) (hv₂ j) (1 : ℝ))⟫) := by
    ext i j
    exact Eq.symm (innerProduct_eq_inter (v i) (v j) (hv₁ i) (hv₁ j) (hv₂ i) (hv₂ j))
  change PosSemidef fun i j ↦ (μ (v i ∩ v j)).toReal
  rw [hf]
  exact IsGram.PosSemidef hg

end L2
