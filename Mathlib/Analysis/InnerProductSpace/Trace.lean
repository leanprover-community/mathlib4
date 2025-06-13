/-
Copyright (c) 2025 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

/-!
# Traces in inner product spaces

This file contains various results about traces of linear operators in inner product spaces.
-/

namespace LinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open scoped InnerProductSpace

lemma trace_eq_sum_inner (T : E →ₗ[𝕜] E) (b : OrthonormalBasis ι 𝕜 E) :
    T.trace 𝕜 E = ∑ i, ⟪b i, T (b i)⟫_𝕜 := by
  let b' := b.toBasis
  rw [LinearMap.trace_eq_matrix_trace 𝕜 b' T]
  apply Fintype.sum_congr
  intro i
  rw [Matrix.diag_apply, T.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
    b.repr_apply_apply]

end LinearMap
