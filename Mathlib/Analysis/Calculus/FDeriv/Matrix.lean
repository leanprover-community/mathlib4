/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Hadamard
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Derivatives of Matrices


-/

variable {ι : Type*} {𝕜 : Type*} {E F : Type*} {A : Type*} {m n p q : Type*}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

namespace Matrix
open scoped Kronecker

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

theorem hasFDerivAt_matrix
    {M : E → Matrix m n F} {x : E} {M' : E →L[𝕜] Matrix m n F} :
    HasFDerivAt M M' x ↔ ∀ i j,
      HasFDerivAt (fun x => M x i j)
        (⟨Matrix.entryLinearMap 𝕜 F i j, continuous_id.matrix_elem i j⟩ ∘L M') x := by
  erw [hasFDerivAt_pi']
  simp_rw [hasFDerivAt_pi', ← ContinuousLinearMap.comp_assoc]
  rfl

-- theorem HasFDerivAt.matrix_mul [NormedRing A] [NormedAlgebra 𝕜 A]
--     {M : E → Matrix m n A} {N : E → Matrix n p A}
--     {M' : E →L[𝕜] Matrix m n A} {N' : E →L[𝕜] Matrix n p A} {x : E}
--     (hM : HasFDerivAt M M' x) (hN : HasFDerivAt N N' x) :
--     HasFDerivAt (fun a => M a * N a) (sorry ∘L M' + sorry ∘L N') x := by
--   rw [hasFDerivAt_matrix] at hM hN ⊢
--   intro i j
--   simp only [mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
--   refine (HasFDerivAt.sum fun k _hk => (hM _ _).mul' (hN _ _)).congr_fderiv ?_
--   ext x
--   simp [Finset.sum_add_distrib]
--   sorry

theorem HasFDerivAt.matrix_trace
    {M : E → Matrix m m F} {x : E} {M' : E →L[𝕜] Matrix m m F}
    (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a).trace)
      (⟨Matrix.traceLinearMap _ _ _, continuous_id.matrix_trace⟩ ∘L M') x :=
  (HasFDerivAt.sum fun i _hi => (hasFDerivAt_matrix.mp hM : _) i i).congr_fderiv <|
    by ext; simp [Matrix.trace]

theorem HasFDerivAt.matrix_transpose
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a)ᵀ)
      (⟨Matrix.transposeLinearEquiv m n 𝕜 F, continuous_id.matrix_transpose⟩ ∘L M') x :=
  hasFDerivAt_matrix.mpr fun i j => (hasFDerivAt_matrix.mp hM : _) j i

theorem HasDerivAt.matrix_conjTranspose
    [StarRing 𝕜] [TrivialStar 𝕜] [StarAddMonoid F] [StarModule 𝕜 F] [ContinuousStar F]
    {M : E → Matrix m n F} {M' : E →L[𝕜] Matrix m n F} {x : E} (hM : HasFDerivAt M M' x) :
    HasFDerivAt (fun a => (M a)ᴴ)
      (⟨{ Matrix.conjTransposeLinearEquiv m n 𝕜 F with map_smul' := by simp},
          continuous_id.matrix_conjTranspose⟩ ∘L M') x :=
  (hasFDerivAt_matrix.mpr fun i j => ((hasFDerivAt_matrix.mp hM : _) j i).star)

end Matrix
