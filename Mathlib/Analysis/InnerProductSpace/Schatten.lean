/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Schatten operators

This file defines the Schatten operators, and the required trace, modulus and polar maps in order
to define them.

## Main definitions
 - `ContinuousLinearMap.trace` the trace for continuous linear maps between Hilbert spaces.

## Implementation details
The current file only uses `E →L[ℂ] E` instead of `E →L[𝕜] E`, since the proof of `traceOfBasis_eq`
relies on CFC and this is currently only defined for the complex maps.

The lemma `traceOfBasis_eq` shows that the trace is independent of basis. Hence, it matters not
which basis we choose for the definition of the map `trace`. Since there always exists at least one
such basis by the theorem `exists_hilbertBasis` we use the axiom of choice to simply choose any.
This mirrors the construction of `LinearMap.trace`.

### ToDo
 - generalize from `E →L[ℂ] E` to `E →L[𝕜] E` once CFC for the latter has been implemented.

-/

public noncomputable section

namespace ContinuousLinearMap

section Trace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ComplexOrder
open scoped ComplexConjugate ENNReal InnerProductSpace

/-- The trace of an operator on `E` for a given basis `b`. -/
@[expose]
def traceOfBasis (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) : ℂ :=
  ∑' i, ⟪b i, A (b i)⟫_ℂ

omit [CompleteSpace E] in
theorem traceOfBasis_def (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) :
    traceOfBasis A b = ∑' i, ⟪b i, A (b i)⟫_ℂ :=
  rfl

theorem traceOfBasis_eq_tsum_enorm_sq {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) :
    traceOfBasis A b = (∑' i, ‖CFC.sqrt A (b i)‖ₑ ^ 2).toReal := by
  rw [traceOfBasis_def, ENNReal.tsum_toReal_eq fun _ ↦ by finiteness, Complex.ofReal_tsum]
  refine tsum_congr fun i ↦ ?_
  conv_lhs => rw [← CFC.sqrt_mul_sqrt_self A, mul_apply_eq_comp,
    ← (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric.apply_clm]
  simp [inner_self_eq_norm_sq_to_K]

theorem traceOfBasis_eq {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι ι' : Type*}
    (b : HilbertBasis ι ℂ E) (b' : HilbertBasis ι' ℂ E) :
    traceOfBasis A b = traceOfBasis A b' := by
  simp_rw [traceOfBasis_eq_tsum_enorm_sq hA]
  congr 2
  set S := CFC.sqrt A
  calc ∑' i, ‖S (b i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪b' j, S (b i)⟫_ℂ‖ₑ ^ 2 := by
        simp [b'.tsum_enorm_inner_sq]
    _ = ∑' j, ∑' i, ‖⟪b i, S (b' j)⟫_ℂ‖ₑ ^ 2 := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun j ↦ tsum_congr fun i ↦ ?_
        rw [← (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric.apply_clm,
          ← inner_conj_symm, RCLike.enorm_conj]
    _ = ∑' j, ‖S (b' j)‖ₑ ^ 2 := by simp [b.tsum_enorm_inner_sq]

omit [CompleteSpace E] in
theorem traceOfBasis_eq_toReal_tsum {A : E →L[ℂ] E} (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) :
    traceOfBasis A b = (∑' i, ENNReal.ofReal (RCLike.re ⟪b i, A (b i)⟫_ℂ)).toReal := by
  rw [traceOfBasis_def, ENNReal.tsum_toReal_eq fun _ ↦ ENNReal.ofReal_ne_top, Complex.ofReal_tsum]
  refine tsum_congr fun i ↦ ?_
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp (by simpa using hA.inner_nonneg_right (b i))
  rw [ENNReal.toReal_ofReal hre]
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr him)).symm

/-- The trace of an operator on `E`. -/
def trace (A : E →L[ℂ] E) : ℂ := traceOfBasis A (exists_hilbertBasis ℂ E).choose_spec.choose

variable (A : E →L[ℂ] E)

@[simp]
theorem trace_zero : trace (0 : E →L[ℂ] E) = 0 := by
  simp [trace, traceOfBasis_def]

@[simp]
theorem trace_smul (c : ℂ) : (c • A).trace = c * A.trace := by
  simp [trace, traceOfBasis_def, ← tsum_mul_left]

theorem trace_adjoint : A.adjoint.trace = conj A.trace := by
  simp [trace, traceOfBasis_def, Complex.conj_tsum, ContinuousLinearMap.adjoint_inner_right]

theorem toLinearMap_trace [FiniteDimensional ℂ E] :
    A.toLinearMap.trace ℂ E = A.trace := by
  unfold trace
  set ι := (exists_hilbertBasis ℂ E).choose
  set b := (exists_hilbertBasis ℂ E).choose_spec.choose
  let : Finite ι := b.orthonormal.linearIndependent.finite
  let : Fintype ι := Fintype.ofFinite ι
  simp [traceOfBasis_def, LinearMap.trace_eq_sum_inner _ b.toOrthonormalBasis]

section IsPositive

variable {A B : E →L[ℂ] E}

theorem trace_eq_traceOfBasis (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) : trace A = traceOfBasis A b := by
  unfold trace
  exact traceOfBasis_eq hA _ b

theorem trace_nonneg (hA : 0 ≤ A) : 0 ≤ A.trace := by
  set b := (exists_hilbertBasis ℂ E).choose_spec.choose
  exact tsum_nonneg fun i ↦ by
    simpa only [sub_zero] using hA.inner_nonneg_right (b i)

theorem trace_add_le (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) ≤ trace A + trace B := by
  simp_rw [trace, traceOfBasis_eq_toReal_tsum (add_nonneg hA hB), traceOfBasis_eq_toReal_tsum hA,
    traceOfBasis_eq_toReal_tsum hB, add_apply, inner_add_right, map_add,
    ENNReal.ofReal_add (hA.of_nonneg.re_inner_nonneg_right _)
      (hB.of_nonneg.re_inner_nonneg_right _), ENNReal.tsum_add]
  exact_mod_cast ENNReal.toReal_add_le

end IsPositive

end Trace

end ContinuousLinearMap
