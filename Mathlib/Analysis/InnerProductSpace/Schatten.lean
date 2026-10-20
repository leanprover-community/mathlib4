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
def traceOfBasis (A : E →L[ℂ] E) {ι : Type*} (b : HilbertBasis ι ℂ E) : ℂ :=
  ∑' i, ⟪b i, A (b i)⟫_ℂ

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
  simp only [Complex.coe_algebraMap, Complex.ofReal_inj]
  have h (i : ι') (j : ι) : ‖⟪b' i, S (b j)⟫_ℂ‖ ^ 2 = ‖⟪b j, S (b' i)⟫_ℂ‖ ^ 2 := by
    rw [← (CFC.sqrt_nonneg A).isSelfAdjoint.isSymmetric.apply_clm (b' i) (b j), norm_inner_symm]
  by_cases hs : Summable (Function.uncurry fun b_1 c ↦ ‖⟪b' b_1, S (b c)⟫_ℂ‖ ^ 2)
  · rw [Summable.tsum_comm hs]
    simp [h]
  · rw [tsum_eq_zero_of_not_summable (fun hsum ↦ by
      have hg : Summable (fun p : ι × ι' ↦ ‖⟪b' p.2, S (b p.1)⟫_ℂ‖ ^ 2) :=
        (summable_prod_of_nonneg (fun _ ↦ by positivity)).2
        ⟨fun c ↦ b'.orthonormal.inner_products_summable (S (b c)), hsum⟩
      exact hs ((Equiv.prodComm ι' ι).summable_iff.2 hg)
    )]
    rw [tsum_eq_zero_of_not_summable (fun hsum ↦ by
      have hf : Summable (fun p : ι' × ι ↦ ‖⟪b p.2, S (b' p.1)⟫_ℂ‖ ^ 2) :=
        (summable_prod_of_nonneg (fun _ ↦ by positivity)).2
        ⟨fun i ↦ b.orthonormal.inner_products_summable (S (b' i)), hsum⟩
      exact hs (hf.congr fun p ↦ (h p.1 p.2).symm)
    )]

/-- The trace of an operator on `E`. -/
def trace (A : E →L[ℂ] E) : ℂ := traceOfBasis A
  (Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E)))

variable {A B : E →L[ℂ] E}

theorem trace_eq_traceOfBasis (hA : 0 ≤ A) {ι : Type*}
    (b : HilbertBasis ι ℂ E) : trace A = traceOfBasis A b := by
  unfold trace
  exact traceOfBasis_eq hA _ b

@[simp]
theorem trace_zero : trace (0 : E →L[ℂ] E) = 0 := by
  simp [trace, traceOfBasis]

variable (A) in
@[simp]
theorem trace_smul (c : ℂ) : (c • A).trace = c * A.trace := by
  simp [trace, traceOfBasis, ← tsum_mul_left]

variable (A) in
theorem trace_adjoint : A.adjoint.trace = conj A.trace := by
  simp [trace, traceOfBasis, Complex.conj_tsum, ContinuousLinearMap.adjoint_inner_right]

theorem trace_nonneg (hA : 0 ≤ A) : 0 ≤ A.trace := by
  unfold trace traceOfBasis
  set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  exact tsum_nonneg fun i ↦ by
    simpa only [sub_zero] using hA.inner_nonneg_right (b i)

variable (A) in
theorem toLinearMap_trace [FiniteDimensional ℂ E] :
    A.toLinearMap.trace ℂ E = A.trace := by
  unfold trace traceOfBasis
  set ι := Classical.choose (exists_hilbertBasis ℂ E)
  set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  let : Finite ι := b.orthonormal.linearIndependent.finite
  let : Fintype ι := Fintype.ofFinite ι
  simp [LinearMap.trace_eq_sum_inner _ b.toOrthonormalBasis]

theorem _root_.Summable.of_add_nonneg {ι : Type*} {f g : ι → ℂ} (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (h : Summable fun i => f i + g i) : Summable f := by
  have h' : Summable fun i => (f i).re := Summable.of_nonneg_of_le
    (fun i => (Complex.nonneg_iff.1 (hf i)).1)
    (fun i => le_add_of_nonneg_right (Complex.nonneg_iff.1 (hg i)).1)
    (by simpa using Complex.reCLM.summable h)
  refine (Complex.summable_ofReal.2 h').congr fun i => ?_
  exact Complex.ext
    (by rw [Complex.ofReal_re])
    (by rw [Complex.ofReal_im]; exact (Complex.nonneg_iff.1 (hf i)).2)

theorem trace_add_le (hA : 0 ≤ A) (hB : 0 ≤ B) : trace (A + B) ≤ trace A + trace B := by
  unfold trace traceOfBasis
  set b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  have hA' : ∀ i, 0 ≤ ⟪b i, A (b i)⟫_ℂ := fun i => by
    simpa only [sub_zero] using hA.inner_nonneg_right (b i)
  have hB' : ∀ i, 0 ≤ ⟪b i, B (b i)⟫_ℂ := fun i => by
    simpa only [sub_zero] using hB.inner_nonneg_right (b i)
  by_cases h : Summable fun i => ⟪b i, (A + B) (b i)⟫_ℂ
  · have hAs : Summable fun i => ⟪b i, A (b i)⟫_ℂ :=
      Summable.of_add_nonneg hA' hB' (h.congr fun i => by rw [add_apply, inner_add_right])
    have hBs : Summable fun i => ⟪b i, B (b i)⟫_ℂ :=
      Summable.of_add_nonneg hB' hA' (h.congr fun i => by rw [add_comm, add_apply, inner_add_right])
    simp_rw [add_apply, inner_add_right]
    rw [hAs.tsum_add hBs]
  · rw [tsum_eq_zero_of_not_summable h]
    exact add_nonneg (tsum_nonneg hA') (tsum_nonneg hB')

end Trace

end ContinuousLinearMap
