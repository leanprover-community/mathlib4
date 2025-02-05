/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Matrix algebra is an Azumaya algebra over R

In this file we prove that finite dimesional matrix algebra `Matrix n n R` over `R`
is an Azumaya algebra where `R` is a commutative ring.

## Main Results

- `IsAzumaya.Matrix`: Finite dimensional matrix algebra over `R` is Azumaya.

-/
open scoped TensorProduct

variable (R n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

noncomputable section

open Matrix MulOpposite

/-- `AlgHom.mulLeftRight` for matrix algebra sends basis Eᵢⱼ⊗Eₖₗ to
  the map `f : Eₛₜ ↦ Eᵢⱼ * Eₛₜ * Eₖₗ = δⱼₛδₜₖEᵢₗ`, therefore we construct the inverse
  by sending `f` to `f(Eⱼₖ)ᵢₗ • Eᵢⱼ⊗Eₖₗ`. -/
abbrev AlgHom.mulLeftRightMatrix_inv :
    Module.End R (Matrix n n R) →ₗ[R] Matrix n n R ⊗[R] (Matrix n n R)ᵐᵒᵖ where
  toFun := fun f ↦ ∑ ⟨⟨i, j⟩, k, l⟩ : (n × n) × n × n,
    f (stdBasisMatrix j k 1) i l • (stdBasisMatrix i j 1) ⊗ₜ[R] op (stdBasisMatrix k l 1)
  map_add' := fun f1 f2 ↦ by simp [add_smul, Finset.sum_add_distrib]
  map_smul' := fun r f ↦ by simp [MulAction.mul_smul, Finset.smul_sum]

lemma AlgHom.mulLeftRightMatrix.inv_comp:
    (AlgHom.mulLeftRightMatrix_inv R n).comp
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap = .id :=
  Basis.ext (Basis.tensorProduct (Matrix.stdBasis _ _ _)
    ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..)))
  fun ⟨⟨i0, j0⟩, k0, l0⟩ ↦ by
    simp [stdBasis_eq_stdBasisMatrix, ite_and, Fintype.sum_prod_type,
      mulLeftRight_apply, stdBasisMatrix, Matrix.mul_apply]

lemma AlgHom.mulLeftRightMatrix.comp_inv:
    (AlgHom.mulLeftRight R (Matrix n n R)).toLinearMap.comp
    (AlgHom.mulLeftRightMatrix_inv R n) = .id := by
  ext f : 1
  apply Basis.ext (Matrix.stdBasis _ _ _)
  intro ⟨i, j⟩
  simp [AlgHom.mulLeftRight_apply, stdBasis_eq_stdBasisMatrix]
  ext k l
  simp [sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, stdBasisMatrix,
    Fintype.sum_prod_type, ite_and]

instance [Inhabited n]: FaithfulSMul R (Matrix n n R) where
  eq_of_smul_eq_smul {r1 r2} h := by
    specialize h 1
    rw [← Matrix.ext_iff] at h
    specialize h default default
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    exact h

namespace IsAzumaya

/-- Matrix ring over `R` is an azumaya algebra over `R`. -/
theorem Matrix [Inhabited n]: IsAzumaya R (Matrix n n R) where
  bij := ⟨Function.HasLeftInverse.injective ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp R n)⟩,
    Function.HasRightInverse.surjective ⟨AlgHom.mulLeftRightMatrix_inv R n,
    DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv R n)⟩⟩

end IsAzumaya

end
