/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Traces in inner product spaces

This file contains various results about traces of linear operators in inner product spaces.
-/

public section

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
  simp [Module.End.trace_eq_sum_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.sum_ofFn]

lemma IsSymmetric.re_trace_eq_sum_eigenvalues {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    RCLike.re (T.trace 𝕜 E) = ∑ i, hT.eigenvalues hn i := by
  rw [hT.trace_eq_sum_eigenvalues]
  exact RCLike.ofReal_re_ax _

open InnerProductSpace in
lemma _root_.InnerProductSpace.trace_rankOne (x y : E) :
    (rankOne 𝕜 x y).trace 𝕜 E = inner 𝕜 y x := by
  rw [rankOne_def', ContinuousLinearMap.coe_comp, trace_comp_comm',
    ← ContinuousLinearMap.coe_comp, ContinuousLinearMap.comp_toSpanSingleton]
  simp [trace_eq_sum_inner _ (OrthonormalBasis.singleton Unit 𝕜)]

end LinearMap
