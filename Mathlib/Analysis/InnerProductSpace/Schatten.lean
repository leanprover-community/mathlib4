/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Schatten operators

This file defines the Schatten operators, and the required trace, modulus and polar maps in order
to define them.

## Main definitions
 - `ContinuousLinearMap.trace` the trace for continuous linear maps between Hilbert spaces.

-/

public noncomputable section

namespace ContinuousLinearMap

section Trace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexConjugate ENNReal InnerProductSpace

/-- The trace of an operator on `E`. -/
def traceOfBasis (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, A (b i)⟫_ℂ)

theorem traceOfBasis_eq {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι ι' : Type*}
    (b : HilbertBasis ι ℂ E) (b' : HilbertBasis ι' ℂ E) :
    traceOfBasis A b = traceOfBasis A b' := by
  unfold traceOfBasis
  set S := CFC.sqrt A with hS
  have hS' : S.adjoint * S = A := by
    simp [hS, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
  simp_rw +singlePass [← hS', mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
    ← b'.tsum_inner_mul_inner (S (b _)), ← inner_conj_symm (S (b _)),
    ← b.tsum_inner_mul_inner (S (b' _)), ← inner_conj_symm (S (b' _)),
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_tsum]
  simp only [Complex.coe_algebraMap, RCLike.re_to_complex, Complex.ofReal_re]
  simp_rw [fun x => ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (b.orthonormal.inner_products_summable x),
    fun x => ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      (b'.orthonormal.inner_products_summable x)]
  rw [ENNReal.tsum_comm]
  simp_rw [← LinearMap.IsSymmetric.apply_clm (T := S)
    (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric (b' _) (b _), norm_inner_symm (S (b' _)) (b _)]

/-- The trace of an operator on `E`. -/
def trace (A : E →L[ℂ] E) : ℝ≥0∞ := traceOfBasis A
  (Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E)))

variable {A B : E →L[ℂ] E}

theorem trace_eq_traceOfBasis (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) : trace A = traceOfBasis A b := by
  unfold trace
  exact traceOfBasis_eq hA _ b

@[simp]
theorem trace_zero : trace (0 : E →L[ℂ] E) = 0 := by simp [trace, traceOfBasis]

theorem trace_add_le : trace (A + B) ≤ trace A + trace B := by
  unfold trace traceOfBasis
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  simp only [add_apply, inner_add_right, map_add]
  exact ENNReal.ofReal_add_le

@[simp]
theorem trace_add (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) = trace A + trace B := by
  unfold trace traceOfBasis
  simp_rw [add_apply, inner_add_right, map_add, ← ENNReal.tsum_add]
  refine tsum_congr fun i ↦ ?_
  refine ENNReal.ofReal_add ?_ ?_
  · simpa only [sub_zero] using hA.re_inner_nonneg_right _
  · simpa only [sub_zero] using hB.re_inner_nonneg_right _

theorem trace_eq_zero (hA : 0 ≤ A) : trace A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  unfold trace traceOfBasis at h
  set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  set S := CFC.sqrt A with hS
  have hS' : S.adjoint * S = A := by
    simp [hS, CFC.sqrt_mul_sqrt_self A hA, (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq]
  simp_rw [ENNReal.tsum_eq_zero, ← hS', mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, ENNReal.ofReal_eq_zero, re_inner_self_nonpos] at h
  rw [← hS']
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  simp [h i]

end Trace

end ContinuousLinearMap
