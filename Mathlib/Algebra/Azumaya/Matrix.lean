/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Matrix algebra is an Azumaya algebra over R

In this file we prove that finite dimensional matrix algebra `Matrix n n R` over `R`
is an Azumaya algebra where `R` is a commutative ring.

## Main Results

- `IsAzumaya.Matrix`: Finite dimensional matrix algebra over `R` is Azumaya.

-/
open scoped TensorProduct

variable (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n]

noncomputable section

open Matrix MulOpposite

/-- `AlgHom.mulLeftRight` for matrix algebra sends basis Eᵢⱼ⊗Eₖₗ to
  the map `f : Eₛₜ ↦ Eᵢⱼ * Eₛₜ * Eₖₗ = δⱼₛδₜₖEᵢₗ`, therefore we construct the inverse
  by sending `f` to `∑ᵢₗₛₜ f(Eₛₜ)ᵢₗ • Eᵢₛ⊗Eₜₗ`. -/
abbrev AlgHom.mulLeftRightMatrix_inv :
    Module.End R (Matrix n n R) →ₗ[R] Matrix n n R ⊗[R] (Matrix n n R)ᵐᵒᵖ where
  toFun f := ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (single j k 1) i l • (single i j 1) ⊗ₜ[R] op (single k l 1)
  map_add' f1 f2 := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r f := by simp [MulAction.mul_smul, Finset.smul_sum]

lemma AlgHom.mulLeftRightMatrix.inv_comp :
    (AlgHom.mulLeftRightMatrix_inv R n).comp
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id :=
  ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..))).ext
  fun ⟨⟨i0, j0⟩, k0, l0⟩ ↦ by
    simp [stdBasis_eq_single, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, single, Matrix.mul_apply]

lemma AlgHom.mulLeftRightMatrix.comp_inv :
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap.comp
    (AlgHom.mulLeftRightMatrix_inv R n) = .id := by
  ext f : 1
  apply (Matrix.stdBasis _ _ _).ext
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_sum,
    map_smul, stdBasis_eq_single, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  ext k l
  simp [sum_apply, Matrix.mul_apply, single, Fintype.sum_prod_type, ite_and]

namespace IsAzumaya

/-- A nontrivial matrix ring over `R` is an Azumaya algebra over `R`. -/
theorem matrix [Nonempty n] : IsAzumaya R (Matrix n n R) where
  eq_of_smul_eq_smul := by nontriviality R; exact eq_of_smul_eq_smul
  bij := Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n),
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩

end IsAzumaya

end
