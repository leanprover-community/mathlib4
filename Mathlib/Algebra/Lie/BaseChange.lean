/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.base_change
! leanprover-community/mathlib commit 9264b15ee696b7ca83f13c8ad67c83d6eb70b730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct

/-!
# Extension and restriction of scalars for Lie algebras

Lie algebras have a well-behaved theory of extension and restriction of scalars.

## Main definitions

 * `LieAlgebra.ExtendScalars.lieAlgebra`
 * `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/


universe u v w w₁ w₂ w₃

open scoped TensorProduct

variable (R : Type u) (A : Type w) (L : Type v)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A` over `R`.

In fact this bracket is fully `A`-bilinear but without a significant upgrade to our mixed-scalar
support in the tensor product library, it is far easier to bootstrap like this, starting with the
definition below. -/
private def bracket' : A ⊗[R] L →ₗ[R] A ⊗[R] L →ₗ[R] A ⊗[R] L :=
  TensorProduct.curry <|
    TensorProduct.map (LinearMap.mul' R _) (LieModule.toModuleHom R L L : L ⊗[R] L →ₗ[R] L) ∘ₗ
      ↑(TensorProduct.tensorTensorTensorComm R A L A L)

@[simp]
private theorem bracket'_tmul (s t : A) (x y : L) :
    bracket' R A L (s ⊗ₜ[R] x) (t ⊗ₜ[R] y) = (s * t) ⊗ₜ ⁅x, y⁆ := by simp [bracket']

instance : Bracket (A ⊗[R] L) (A ⊗[R] L) where bracket x y := bracket' R A L x y

private theorem bracket_def (x y : A ⊗[R] L) : ⁅x, y⁆ = bracket' R A L x y :=
  rfl

@[simp]
theorem bracket_tmul (s t : A) (x y : L) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s * t) ⊗ₜ ⁅x, y⁆ := by
  rw [bracket_def, bracket'_tmul]
#align lie_algebra.extend_scalars.bracket_tmul LieAlgebra.ExtendScalars.bracket_tmul

private theorem bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine' x.induction_on _ _ _
  · simp only [LinearMap.map_zero, eq_self_iff_true, LinearMap.zero_apply]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, eq_self_iff_true, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L z₁ z₂ + bracket' R A L z₂ z₁ = 0 by
      rw [LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
        zero_add, add_zero, add_comm, this]
    refine' z₁.induction_on _ _ _
    · simp only [LinearMap.map_zero, add_zero, LinearMap.zero_apply]
    · intro a₁ l₁; refine' z₂.induction_on _ _ _
      · simp only [LinearMap.map_zero, add_zero, LinearMap.zero_apply]
      · intro a₂ l₂
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, TensorProduct.tmul_neg, bracket'_tmul,
          add_right_neg]
      · intro y₁ y₂ hy₁ hy₂
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, LinearMap.add_apply, LinearMap.map_add]
    · intro y₁ y₂ hy₁ hy₂
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, LinearMap.add_apply, LinearMap.map_add]

private theorem bracket_leibniz_lie (x y z : A ⊗[R] L) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  -- Porting note: replaced some `simp`s by `rw`s to avoid raising heartbeats
  simp only [bracket_def]
  refine' x.induction_on _ _ _
  · simp only [LinearMap.map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine' y.induction_on _ _ _
    · simp only [LinearMap.map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine' z.induction_on _ _ _
      · rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero,
          add_zero]
      · intro a₃ l₃; simp only [bracket'_tmul]
        rw [mul_left_comm a₂ a₁ a₃, mul_assoc, leibniz_lie, TensorProduct.tmul_add]
      · intro u₁ u₂ h₁ h₂
        rw [map_add, map_add, map_add, map_add, map_add, h₁, h₂, add_add_add_comm]
    · intro u₁ u₂ h₁ h₂
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, map_add, map_add,
        LinearMap.add_apply, h₁, h₂, add_add_add_comm]
  · intro u₁ u₂ h₁ h₂
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, map_add, map_add,
      LinearMap.add_apply, h₁, h₂, add_add_add_comm]

instance : LieRing (A ⊗[R] L) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, LinearMap.map_add]
  lie_add x y z := by simp only [bracket_def, LinearMap.map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L

private theorem bracket_lie_smul (a : A) (x y : A ⊗[R] L) : ⁅x, a • y⁆ = a • ⁅x, y⁆ := by
  refine' x.induction_on _ _ _
  · simp only [zero_lie, smul_zero]
  · intro a₁ l₁; refine' y.induction_on _ _ _
    · simp only [lie_zero, smul_zero]
    · intro a₂ l₂
      simp only [bracket_def, bracket', TensorProduct.smul_tmul', mul_left_comm a₁ a a₂,
        TensorProduct.curry_apply, LinearMap.mul'_apply, Algebra.id.smul_eq_mul,
        Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_comp, TensorProduct.map_tmul,
        TensorProduct.tensorTensorTensorComm_tmul]
    · intro z₁ z₂ h₁ h₂
      simp only [h₁, h₂, smul_add, lie_add]
  · intro z₁ z₂ h₁ h₂
    simp only [h₁, h₂, smul_add, add_lie]

instance lieAlgebra : LieAlgebra A (A ⊗[R] L) where lie_smul := bracket_lie_smul R A L
#align lie_algebra.extend_scalars.lie_algebra LieAlgebra.ExtendScalars.lieAlgebra

end ExtendScalars

namespace RestrictScalars

open RestrictScalars

variable [h : LieRing L]

instance : LieRing (RestrictScalars R A L) :=
  h

variable [CommRing A] [LieAlgebra A L]

instance lieAlgebra [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A L) where
  lie_smul t x y := (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) : _)
#align lie_algebra.restrict_scalars.lie_algebra LieAlgebra.RestrictScalars.lieAlgebra

end RestrictScalars

end LieAlgebra
