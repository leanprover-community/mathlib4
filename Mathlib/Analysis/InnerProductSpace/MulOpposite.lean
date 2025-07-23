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

/-- The inner product of `Hᵐᵒᵖ` is given by `⟪x, y⟫ ↦ ⟪x.unop, y.unop⟫`. -/
@[instance]
def MulOpposite.hasInner [Inner 𝕜 H] :
    Inner 𝕜 Hᵐᵒᵖ where inner x y := inner 𝕜 x.unop y.unop

@[simp]
theorem inner_unop [Inner 𝕜 H] (x y : Hᵐᵒᵖ) :
    inner 𝕜 x.unop y.unop = inner 𝕜 x y := rfl

open MulOpposite in
@[simp]
theorem inner_op [Inner 𝕜 H] (x y : H) :
    inner 𝕜 (op x) (op y) = inner 𝕜 x y := rfl

variable [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

instance MulOpposite.innerProductSpace : InnerProductSpace 𝕜 Hᵐᵒᵖ where
  norm_sq_eq_re_inner x := (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

theorem Basis.mulOpposite_is_orthonormal_iff {ι : Type*} (b : Basis ι 𝕜 H) :
    Orthonormal 𝕜 b.mulOpposite ↔ Orthonormal 𝕜 b := Iff.rfl

/-- The mulOpposite of an orthonormal basis. -/
noncomputable def OrthonormalBasis.mulOpposite {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ := Basis.toOrthonormalBasis b.toBasis.mulOpposite b.orthonormal

/-- The adjoint of `MulOpposite.opContinuousLinearEquiv` is its inverse. -/
theorem MulOpposite.opContinuousLinearEquiv_adjoint [CompleteSpace H] :
    ContinuousLinearMap.adjoint (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=H)).toContinuousLinearMap
      = (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=H)).symm.toContinuousLinearMap := by
  ext x
  apply ext_inner_left 𝕜
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
    opContinuousLinearEquiv_apply, ← inner_unop, unop_op, opContinuousLinearEquiv_symm_apply]

theorem MulOpposite.opContinuousLinearEquiv_isometry
    {R M : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M] :
    Isometry (MulOpposite.opContinuousLinearEquiv R (M:=M)) := fun _ _ => rfl

theorem MulOpposite.opLinearEquiv_adjoint [FiniteDimensional 𝕜 H] :
    LinearMap.adjoint (MulOpposite.opLinearEquiv 𝕜 (M:=H)).toLinearMap
      = (MulOpposite.opLinearEquiv 𝕜 (M:=H)).symm.toLinearMap := by
  have := FiniteDimensional.complete 𝕜 H
  calc _ = (ContinuousLinearMap.adjoint
      (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=H)).toContinuousLinearMap).toLinearMap := rfl
    _ = _ := by rw [MulOpposite.opContinuousLinearEquiv_adjoint]; rfl
