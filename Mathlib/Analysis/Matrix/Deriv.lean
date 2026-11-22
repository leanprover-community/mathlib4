/-
Copyright (c) 2026 Levent Alpöge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Levent Alpöge
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Jacobi's formula for the derivative of the determinant

This file proves **Jacobi's formula**: along a path `G` of square matrices whose entries `G s i j`
are differentiable at `t` with derivatives `G' i j`, the function `s ↦ (G s).det` is
differentiable at `t` with derivative `((G t).adjugate * G').trace`.
As a corollary, when `G t` is positive definite, `s ↦ log ((G s).det).re` is differentiable at
`t` with derivative `((G t)⁻¹ * G').trace.re`.

## Main results

* `Matrix.hasDerivAt_det`: Jacobi's formula.
* `Matrix.hasDerivAt_log_det_re`: the derivative of the logarithm of the determinant along a path of
  positive definite matrices.

## Tags

determinant, derivative, Jacobi's formula, Liouville formula
-/

@[expose] public section

open Matrix

open scoped ComplexOrder

namespace Matrix

section Jacobi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {𝔸 : Type*} [NormedCommRing 𝔸]
  [NormedAlgebra 𝕜 𝔸] {n : Type*} [Fintype n] [DecidableEq n]

/-- Expansion of the trace of `A.adjugate * B` obtained by applying the Leibniz formula to
`Matrix.det_eq_sum_mul_adjugate_col`. -/
private theorem trace_adjugate_mul_eq_sum_perm (A B : Matrix n n 𝔸) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : 𝔸) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by
  have hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : 𝔸) *
      ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i) := by
    intro i
    have h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]
    congr 1
    all_goals first
      | refine Finset.prod_congr rfl fun j hj => ?_
        simp [Finset.ne_of_mem_erase hj]
      | simp
  simp only [Matrix.trace, Matrix.diag, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

/-- **Jacobi's formula**: if every entry of a path `G` of matrices is differentiable at `t` with
derivative `G' i j`, then `s ↦ (G s).det` is differentiable at `t` with derivative
`((G t).adjugate * G').trace`. -/
theorem hasDerivAt_det (G : 𝕜 → Matrix n n 𝔸) (G' : Matrix n n 𝔸) (t : 𝕜)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by
  rw [trace_adjugate_mul_eq_sum_perm]
  have hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm n,
      ((Equiv.Perm.sign σ : ℤ) : 𝔸) * ∏ j, G s (σ j) j := by
    funext s; exact Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      HasDerivAt (fun s => ((Equiv.Perm.sign σ : ℤ) : 𝔸) * ∏ j, G s (σ j) j)
        (((Equiv.Perm.sign σ : ℤ) : 𝔸) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t :=
    fun σ _ => (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _
  exact HasDerivAt.fun_sum hσ

end Jacobi

section LogDet

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The derivative of `s ↦ log ((G s).det).re` at `t`, where `G t` is positive definite, is
`((G t)⁻¹ * G').trace.re`. -/
theorem hasDerivAt_log_det_re (G : ℝ → Matrix n n 𝕜) (G' : Matrix n n 𝕜) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (RCLike.re (G s).det)) (RCLike.re ((G t)⁻¹ * G').trace) t := by
  have hd : HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t :=
    hasDerivAt_det G G' t hG
  have hre : HasDerivAt (fun s => RCLike.re (G s).det)
      (RCLike.re ((G t).adjugate * G').trace) t := by
    have := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa [Function.comp_def] using this
  have hre0 : 0 < RCLike.re (G t).det ∧ RCLike.im (G t).det = 0 := RCLike.pos_iff.1 hpos.det_pos
  have hlog := hre.log hre0.1.ne'
  convert hlog using 1
  have hdet : (G t).det = ((RCLike.re (G t).det : ℝ) : 𝕜) := RCLike.ext (by simp) (by simp [hre0.2])
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet,
    ← RCLike.ofReal_inv, RCLike.re_ofReal_mul]
  simp only [RCLike.ofReal_re]
  ring

end LogDet

end Matrix
