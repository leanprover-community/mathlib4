/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

/-!
# Direct formula for trace of linear map with respect to an orthonormal basis
-/

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma trace_eq_sum_inner_base_app_base (b : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] E) :
    LinearMap.trace 𝕜 E T = ∑i : ι, inner 𝕜 (b i) (T (b i)) := by
  let b' := b.toBasis
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b' T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply, T.toMatrix_apply]
  rw [b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply]

end OrthonormalBasis
