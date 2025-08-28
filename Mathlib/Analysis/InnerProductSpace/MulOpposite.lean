/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.MulOpposite

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

/-- The multiplicative opposite of an orthonormal basis `b`, i.e., `b i ↦ op (b i)`. -/
noncomputable def _root_.OrthonormalBasis.mulOpposite {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ := b.toBasis.mulOpposite.toOrthonormalBasis b.orthonormal

theorem isometry_opLinearEquiv {R M : Type*} [Semiring R] [SeminormedAddCommGroup M] [Module R M] :
    Isometry (opLinearEquiv R (M:=M)) := fun _ _ => rfl

variable (𝕜 H) in
/-- The linear isometry equivalence version of the function `op`. -/
@[simps!]
def opLinearIsometryEquiv : H ≃ₗᵢ[𝕜] Hᵐᵒᵖ where
  toLinearEquiv := opLinearEquiv 𝕜
  norm_map' _ := rfl

@[simp]
theorem toLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv 𝕜 H).toLinearEquiv = opLinearEquiv 𝕜 := rfl

@[simp]
theorem toContinuousLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv 𝕜 H).toContinuousLinearEquiv = opContinuousLinearEquiv 𝕜 := rfl

end MulOpposite
