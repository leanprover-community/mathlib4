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
Results require `𝕜 = ℝ` or `ℂ`.

## Main definition

* `Matrix.Gram` : a matrix `M : Matrix n n 𝕜` is a Gram matrix if
`M i j = ⟪v i, v j⟫` for all `i j : n`, where
`v : n → α` for an `InnerProductSpace α`.

## Main results

* `Matrix.Gram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix MeasureTheory

variable {α E n 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def Gram (v : n → E) : Matrix n n 𝕜 := fun i j ↦ ⟪v i, v j⟫

/-- Special case of a Gram matrix where te underlying inner product space is an L2-space. -/
noncomputable def L2Gram [MeasurableSpace α] {μ : Measure α} (v : n →  (α →₂[μ] 𝕜)) :
  Matrix n n 𝕜 := Gram v

namespace Matrix

def IsGram (M : Matrix n n 𝕜) (v : n → E) : Prop := (M = Gram v)

end Matrix

lemma IsGram_of_Gram (v : n → E) (M : Matrix n n 𝕜) (hM : IsGram M v) : IsGram (M) v := by
  sorry

lemma IsGram_of_L2Gram [MeasurableSpace α] {μ : Measure α} (v : n →  (α →₂[μ] 𝕜)) :
    IsGram (L2Gram v) v := by
  rfl

lemma IsHermitian (M : Matrix n n ℝ) {v : n → E} (hM : Gram M v) : M.IsHermitian := by
  refine IsHermitian.ext_iff.mpr ?_
  intro i j
  rw [hM, hM]
  simp only [RCLike.star_def, inner_conj_symm]





open NNReal

def v (J : Finset ℝ≥0)


-- def IsGram (M : Matrix n n ℝ) : Prop := ∃ v : n → E, M.Gram v

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

section covariance

open Set ENNReal MeasureTheory

def covariance' [MeasurableSpace E] {μ : Measure E} (J : Finset (E →₂[μ] ℝ)) : Matrix J J ℝ :=
  fun f g => ⟪f.val, g.val⟫

sorry

#check fun f g => ⟪f, g⟫




theorem l [MeasurableSpace E] {μ : Measure E} (J : Finset (Set E)) (hJ₁ : ∀ j ∈ J, MeasurableSet j)
   (hJ₂ : ∀ j ∈ J, μ j ≠ ∞) :
    Gram (fun i j ↦ (covariance' (μ := μ) J i j).toReal)
    (fun i ↦ indicatorConstLp 2 (hJ₁ i.val i.prop) (hJ₂ i.val i.prop) (1 : ℝ)) := by

  sorry

end covariance


open Set ENNReal MeasureTheory

def covariance (J : Finset NNReal) : Matrix J J ℝ≥0∞ :=
  (fun i j => i ⊓ j)





-- variable [MeasurableSpace E] {μ : Measure E}


lemma l1 (s t : E) (v w : E →₂[μ] ℝ) (hv : v = ofIcc s) (hw : w = ofIcc t) :
    ⟪v, w⟫ = ∫ a : E, ⟪v a, w a⟫ ∂μ := by
  exact L2.inner_def v w




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

variable {α M : Type*} [MulZeroClass M]

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


variable [Lattice E] [OrderBot E] [MeasurableSpace E] [TopologicalSpace E]
    [OrderClosedTopology E] [OpensMeasurableSpace E] [CompactIccSpace E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ]

noncomputable def ofIcc (t : E) : E →₂[μ] ℝ :=
  indicatorConstLp 2 (measurableSet_Icc (a := ⊥) (b := t))
    (IsCompact.measure_ne_top isCompact_Icc) 1

#check ofIcc

lemma l1 (s t : E) (v w : E →₂[μ] ℝ) (hv : v = ofIcc s) (hw : w = ofIcc t) :
    ⟪v, w⟫ = ∫ a : E, ⟪v a, w a⟫ ∂μ := by
  exact L2.inner_def v w

open Set

example (s t x : E) :
  (Set.indicator (Icc ⊥ s) (fun _ => 1) x) * (Set.indicator (Icc ⊥ t) (fun _ => 1) x) =
    Set.indicator ((Icc ⊥ s) ∩ (Icc ⊥ t)) (fun _ => 1) x := by
  rw [← Set.indicator_indicator]


  sorry

lemma l2 (s t : E) (v w : E →₂[μ] ℝ) (hv : v = ofIcc s) (hw : w = ofIcc t) (a : E) :
    ⟪v a, w a⟫ = (ofIcc (s ⊓ t) : E →₂[μ] ℝ) a := by
  rw [hv, hw, ofIcc, indicatorConstLp, MemLp.toLp]
  simp only [hv, hw, ofIcc, inner_apply, conj_trivial]
  simp only [Icc_bot, MemLp.toLp, Set.indicator, indicatorConstLp]

  sorry
