/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator


/-! # Gram Matrices

This file defines Gram matrices and proves their positive semi-definiteness.
Results require `𝕜 = ℝ` or `ℂ`.

## Main definition

* `Matrix.Gram` : a matrix `M : Matrix n n 𝕜` is a Gram matrix if
`M i j = ⟪v i, v j⟫` for all `i j : n`, where
`v : n → E` for an `InnerProductSpace E`.

## Main results

* `Matrix.Gram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {E F n : Type*}

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def Gram (M : Matrix n n ℝ) (v : n → E) : Prop := ∀ i j, M i j = ⟪v i, v j⟫

namespace Gram

theorem entry {M : Matrix n n ℝ} {v : n → E} (hM : M.Gram v) (i j : n) : M i j = ⟪v i, v j⟫ :=
  hM i j

lemma IsHermitian (M : Matrix n n ℝ) {v : n → E} (hM : Gram M v) : M.IsHermitian := by
  refine IsHermitian.ext_iff.mpr ?_
  intro i j
  rw [hM, hM]
  simp only [RCLike.star_def, inner_conj_symm]

variable {m : Type*} [Fintype m] [Fintype n]

example (a : ℝ) (x : m → ℝ) : a * ∑ i, x i = ∑ i, a * (x i) := by
  rw [Finset.mul_sum]

example (M : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    x ⬝ᵥ M *ᵥ y = ∑ i, ∑ j, (x i) * (M i j) * (y j) := by
  simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec]
  rfl

theorem PosSemidef (M : Matrix n n ℝ) {v : n → E} (hM : M.Gram v) : PosSemidef M := by
  refine ⟨Gram.IsHermitian M hM, fun x ↦ ?_⟩
  let y := ∑ (i : n), x i • v i
  have h : inner y y = (star x ⬝ᵥ M *ᵥ x) := by
    calc
      inner y y = (∑ (i : n), ∑ (j : n), (x i) * (x j) * (inner (v i) (v j))) := by
          simp_rw [y, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
          simp only [conj_trivial, y]
        _ = (∑ (i : n), ∑ (j : n), (x i) * (x j) * (M i j)) := by
          simp_rw [hM.entry]
        _ = (x ⬝ᵥ M *ᵥ x) := by
          simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm]
  refine nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [← h]
    exact real_inner_self_nonneg
  · simp only [im_to_real]


end Gram

end Matrix

open Set NNReal MeasureTheory

def covariance (J : Finset NNReal) : Matrix J J ℝ≥0 :=
  (fun i j => i ⊓ j)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

example (t : ℝ) : MeasurableSet (Icc 0 t) := by exact measurableSet_Icc

example [MeasurableSpace E] {μ : Measure E} [TopologicalSpace E] [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hK : IsCompact K) : μ K < ⊤ := by
  exact IsCompact.measure_lt_top hK



example [Preorder E] [OrderBot E] [MeasurableSpace E] {μ : Measure E} [TopologicalSpace E]
  [CompactIccSpace E] [IsFiniteMeasureOnCompacts μ] (t : E) :
      μ (Icc ⊥ t) ≠ ⊤ :=
    by
  exact IsCompact.measure_ne_top isCompact_Icc

example [Preorder E] [OrderBot E] [MeasurableSpace E] [TopologicalSpace E]
[OpensMeasurableSpace E]  [OrderClosedTopology E] (t : E) :
      (MeasurableSet (Icc ⊥ t)) :=
    by
  apply measurableSet_Icc

example [Lattice E] [OrderBot E] (s t : E) : (Icc ⊥ s) ∩ (Icc ⊥ t) = (Icc ⊥ (s ⊓ t)) := by
  have h : ⊥ = ((⊥ : E) ⊔ ⊥)  := by
    simp only [le_refl, sup_of_le_left]
  nth_rewrite 3 [h]
  rw [Icc_inter_Icc]

def v [NormedAddCommGroup F] [Lattice E] [OrderBot E] [MeasurableSpace E] [TopologicalSpace E]
  [CompactIccSpace E] {μ : Measure E} {_ : IsFiniteMeasureOnCompacts μ} : E →₂[μ] F := by
    have h (t : E) := isCompact_Icc (a := ⊥) (b := t)
    have h' (t : E) : μ (Icc ⊥ t) ≠ ⊤ := IsCompact.measure_ne_top (h t)
    -- IsCompact.measure_ne_top <|
    exact indicatorConstLp 2  measurableSet_Icc -- (IsCompact.measure_ne_top isCompact_Icc)
