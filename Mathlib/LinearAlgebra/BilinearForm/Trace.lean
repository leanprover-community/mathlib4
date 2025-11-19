/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The trace of a bilinear form
-/

variable {ι ι' R M N : Type*}

noncomputable section

namespace LinearMap
namespace BilinMap
open scoped Matrix
open LinearMap (BilinMap BilinForm)

section Module

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- The trace of a bilinear map with respect to a basis. -/
def traceAux (b : Basis ι R M) : BilinMap R M N →ₗ[R] N :=
  Matrix.traceLinearMap ι R N ∘ₗ LinearMap.toMatrix₂ (N₂ := N) b b

theorem traceAux_apply (b : Basis ι R M) (f : BilinMap R M N) :
    traceAux b f = Matrix.trace (toMatrix₂ b b f) :=
  rfl

/-- `traceAux` is invariant to the basis, so long as the transformation between the bases is
orthogonal. -/
theorem traceAux_basis_congr
    (b : Basis ι R M) (c : Basis ι' R M) (h : c.toMatrix b * (c.toMatrix b)ᵀ = 1) :
    traceAux b = traceAux (N := R) c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix₂ b b f) =
          Matrix.trace (LinearMap.toMatrix₂ b b (f.compl₁₂ .id .id)) := by
        rw [LinearMap.compl₁₂_id_id]
      _ = Matrix.trace ((c.toMatrix b)ᵀ * toMatrix₂ c c f * c.toMatrix b) := by
        rw [LinearMap.toMatrix₂_compl₁₂ c c, toMatrix_id_eq_basis_toMatrix]
      _ = Matrix.trace (toMatrix₂ c c f * (c.toMatrix b * (c.toMatrix b)ᵀ)) := by
        rw [← Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
      _ = Matrix.trace (LinearMap.toMatrix₂ c c f) := by rw [h, mul_one]

end Module

section InnerProductSpace

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable [NormedAddCommGroup M] [InnerProductSpace ℝ M]
variable [NormedAddCommGroup N] [InnerProductSpace ℝ N]

theorem traceAux_orthonormalBasis_congr
    (b : OrthonormalBasis ι ℝ M) (c : OrthonormalBasis ι' ℝ M) :
    traceAux b.toBasis = traceAux (N := ℝ) c.toBasis := by
  refine traceAux_basis_congr _ _ ?_
  simp only [OrthonormalBasis.coe_toBasis, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [c.toMatrix_orthonormalBasis_self_mul_conjTranspose b]

open scoped Classical in
/-- The trace of a bilinear form, corresponding to the trace of `LinearMap.toMatrix₂`.

If no finite orthonormal basis exists, the trace is defined as zero. -/
def trace : BilinForm ℝ M →ₗ[ℝ] ℝ :=
  if H : ∃ s : Finset M, Nonempty (OrthonormalBasis s ℝ M) then
    traceAux H.choose_spec.some.toBasis
  else
    0

/-- Auxiliary lemma for `trace_eq_matrixTrace`. -/
theorem trace_eq_matrixTrace_of_finset {s : Finset M} [DecidableEq M]
    (b : OrthonormalBasis s ℝ M) (f : BilinForm ℝ M) :
    trace f = Matrix.trace (LinearMap.toMatrix₂ b.toBasis b.toBasis f) := by
  have : ∃ s : Finset M, Nonempty (OrthonormalBasis s ℝ M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← traceAux_apply]
  congr 1
  convert traceAux_orthonormalBasis_congr _ _

/-- Any choice of orthonormal basis can be used to expand the trace -/
theorem trace_eq_matrixTrace (b : OrthonormalBasis ι ℝ M) (f : BilinForm ℝ M) :
    trace f = Matrix.trace (LinearMap.toMatrix₂ b.toBasis b.toBasis f) := by
  classical
  have : OrthonormalBasis (Finset.univ.image b) ℝ M :=
    b.reindex (Equiv.ofInjective b b.toBasis.injective |>.trans <| .subtypeEquivProp <| by simp)
  rw [trace_eq_matrixTrace_of_finset this, ← traceAux_apply, ← traceAux_apply,
    traceAux_orthonormalBasis_congr this b]

end InnerProductSpace

end BilinMap
end LinearMap
