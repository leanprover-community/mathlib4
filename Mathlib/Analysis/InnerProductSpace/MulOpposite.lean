/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner product space on `Hᵐᵒᵖ`

This file defines the inner product space structure on `Hᵐᵒᵖ` where we define
the inner product naturally. We also define `OrthonormalBasis.mulOpposite`.
-/

variable {𝕜 H : Type*}

namespace MulOpposite

open MulOpposite

/-- The inner product of `Hᵐᵒᵖ` is given by `⟪x, y⟫ ↦ ⟪x.unop, y.unop⟫`. -/
instance [Inner 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ where inner x y := inner 𝕜 x.unop y.unop

@[simp] theorem inner_unop [Inner 𝕜 H] (x y : Hᵐᵒᵖ) : inner 𝕜 x.unop y.unop = inner 𝕜 x y := rfl

@[simp] theorem inner_op [Inner 𝕜 H] (x y : H) : inner 𝕜 (op x) (op y) = inner 𝕜 x y := rfl

variable [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

instance : InnerProductSpace 𝕜 Hᵐᵒᵖ where
  norm_sq_eq_re_inner x := (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

theorem _root_.Module.Basis.mulOpposite_is_orthonormal_iff {ι : Type*} (b : Module.Basis ι 𝕜 H) :
    Orthonormal 𝕜 b.mulOpposite ↔ Orthonormal 𝕜 b := Iff.rfl

/-- The mulOpposite of an orthonormal basis. -/
noncomputable def _root_.OrthonormalBasis.mulOpposite {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ := Module.Basis.toOrthonormalBasis b.toBasis.mulOpposite b.orthonormal

/-- The adjoint of `MulOpposite.opContinuousLinearEquiv` is its inverse. -/
theorem opContinuousLinearEquiv_adjoint [CompleteSpace H] :
    ContinuousLinearMap.adjoint (opContinuousLinearEquiv 𝕜 (M:=H)).toContinuousLinearMap
      = (opContinuousLinearEquiv 𝕜 (M:=H)).symm.toContinuousLinearMap := by
  ext x
  apply ext_inner_left 𝕜
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
    opContinuousLinearEquiv_apply, ← inner_unop, unop_op, opContinuousLinearEquiv_symm_apply]

theorem opContinuousLinearEquiv_isometry
    {R M : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M] :
    Isometry (opContinuousLinearEquiv R (M:=M)) := fun _ _ => rfl

theorem opLinearEquiv_adjoint [FiniteDimensional 𝕜 H] :
    LinearMap.adjoint (opLinearEquiv 𝕜 (M:=H)).toLinearMap
      = (opLinearEquiv 𝕜 (M:=H)).symm.toLinearMap :=
  have := FiniteDimensional.complete 𝕜 H
  calc _ = (ContinuousLinearMap.adjoint
      (opContinuousLinearEquiv 𝕜 (M:=H)).toContinuousLinearMap).toLinearMap := rfl
    _ = _ := by rw [opContinuousLinearEquiv_adjoint]; rfl

end MulOpposite
