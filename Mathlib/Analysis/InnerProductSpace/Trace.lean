/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace

/-!
# Traces in inner product spaces

This file contains various results about traces of linear operators in inner product spaces.
-/

namespace LinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

lemma trace_eq_sum_inner (T : E →ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E) :
    T.trace 𝕜 E = ∑ i, ⟪b i, T (b i)⟫_𝕜 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b.toBasis T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply, T.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
    b.repr_apply_apply]

variable [FiniteDimensional 𝕜 E]
variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)

lemma IsSymmetric.trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    T.trace 𝕜 E = ∑ i, hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  rw [T.trace_eq_sum_inner b, RCLike.ofReal_sum]
  apply Fintype.sum_congr
  intro i
  rw [hT.apply_eigenvectorBasis, inner_smul_real_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
  simp [RCLike.ofReal_alg]

lemma IsSymmetric.re_trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.trace 𝕜 E) = ∑ i, hT.eigenvalues hn i := by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

end LinearMap

namespace InnerProductSpace
open ContinuousLinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma sum_rankOne_OrthonormalBasis (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) = 1 := by
  ext x
  simp only [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, one_apply,
    b.sum_repr' x]

lemma trace_toLinearMap_rankOne (x y : E) (b : Module.Basis ι 𝕜 E) :
    (InnerProductSpace.rankOne 𝕜 x y).trace 𝕜 E = inner 𝕜 y x := by
  have : Module.Finite 𝕜 E := Module.Finite.of_basis b
  rw [rankOne_def, coe_comp, LinearMap.trace_comp_comm', ← coe_comp, comp_lsmul_flip_apply]
  simp [LinearMap.trace_eq_sum_inner _ ((Module.Basis.singleton Unit 𝕜).toOrthonormalBasis
    (by simp [orthonormal_iff_ite]))]

end InnerProductSpace
