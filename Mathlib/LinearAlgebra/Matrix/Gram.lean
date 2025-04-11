/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Algebra.GroupWithZero.Defs

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semi-definiteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.Gram` : a matrix `M : Matrix n n 𝕜` is a Gram matrix if
`M i j = ⟪v i, v j⟫` for all `i j : n`, where
`v : n → α` for an `InnerProductSpace α`.

## Main results

* `Matrix.Gram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix MeasureTheory

open scoped InnerProductSpace

namespace Matrix

variable {E n : Type*}
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def Gram (𝕜 : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : n → E) : Matrix n n 𝕜  := fun i j ↦ inner (v i) (v j)

local notation "⟪" x ", " y "⟫" => @inner 𝕜  _ _ x y

/-- Special case of a Gram matrix where the underlying inner product space is an L2-space. -/
noncomputable def L2Gram (v : n → (α →₂[μ] 𝕜)) :
  Matrix n n 𝕜 := Gram 𝕜 v

def IsGram (M : Matrix n n 𝕜) (v : n → E) : Prop := (M = Gram 𝕜 v)

namespace IsGram

lemma of_Gram (v : n → E) : IsGram (Gram 𝕜 v) v := by
  rfl

lemma of_L2Gram (v : n →  (α →₂[μ] 𝕜)) : IsGram (L2Gram v) v := by
  rfl

lemma entry {M : Matrix n n 𝕜} {v : n → E} (hM : IsGram M v) (i j : n) : M i j = ⟪v i, v j⟫ := by
  rw [hM, Gram]

/-- A Gram matrix is Hermitian. -/
lemma IsHermitian {M : Matrix n n 𝕜} {v : n → E} (hM : IsGram M v) : M.IsHermitian := by
  refine IsHermitian.ext_iff.mpr ?_
  intro i j
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

section covariance

variable {E n : Type*}
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {M : Type*} [MulZeroClass M]

omit [MeasurableSpace α] in
lemma Set.indicator_mul_eq_inter (s t : Set α) (f g : α → M) (x : α) :
  (Set.indicator s f x) * (Set.indicator t g x) =
    Set.indicator (s ∩ t) (f * g) x := by
  by_cases h : x ∈ s ∩ t
  · rw [Set.indicator_of_mem h (f * g), Set.indicator_of_mem (mem_of_mem_inter_left h) f,
      Set.indicator_of_mem (mem_of_mem_inter_right h) g]
    simp only [Pi.mul_apply]
  · have g : x ∉ s ∨ x ∉ t := by
      exact Classical.not_and_iff_not_or_not.mp h
    rcases g with (g1 | g2)
    · rw [Set.indicator_of_not_mem g1 f, Set.indicator_of_not_mem h (f * g)]
      let y := (t.indicator g x)
      rw [MulZeroClass.zero_mul]
    · rw [Set.indicator_of_not_mem g2 g, Set.indicator_of_not_mem h (f * g)]
      simp only [mul_zero]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

open MeasureTheory L2

example (f g : α → ℝ) (s : Set α) (hs : MeasurableSet s) (hfg : f =ᶠ[ae μ] g) :
    ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ := by
  refine setIntegral_congr_ae hs ?_
  exact Filter.Eventually.mono hfg fun x a a_1 ↦ a

lemma innerProduct_eq_inter (v w : (Set α)) (hv₁ : MeasurableSet v)
  (hw₁ : MeasurableSet w) (hv₂ : μ v ≠ ⊤) (hw₂ : μ w ≠ ⊤) :
  ⟪((indicatorConstLp 2 hv₁ hv₂ (1 : ℝ))), (indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) ⟫ =
    (μ (v ∩ w)).toReal := by
  rw [inner_indicatorConstLp_one]
  have h : ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) =ᶠ[ae μ] w.indicator fun x ↦ (1 : ℝ) :=
    indicatorConstLp_coeFn (hs := hw₁) (hμs := hw₂)
  have g : ∀ᵐ (x : α) ∂μ, x ∈ v → ((indicatorConstLp 2 hw₁ hw₂ (1 : ℝ)) : α → ℝ) x =
      w.indicator (fun x ↦ (1 : ℝ)) x := by
    exact Filter.Eventually.mono h fun x a a_1 ↦ a
  rw [setIntegral_congr_ae hv₁ g]
  rw [setIntegral_indicator hw₁]
  simp only [integral_const, MeasurableSet.univ,
    Measure.restrict_apply, Set.univ_inter, smul_eq_mul, mul_one]


def covMatrix (v : n → (Set α)) (hv₁ : ∀ j, MeasurableSet (v j))
   (hv₂ : ∀ j, μ (v j) ≠ ⊤) : Matrix n n ℝ := fun i j ↦ (μ (v i ∩ v j)).toReal



end covariance
