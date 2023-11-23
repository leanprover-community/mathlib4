/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

#align_import algebra.lie.base_change from "leanprover-community/mathlib"@"9264b15ee696b7ca83f13c8ad67c83d6eb70b730"

/-!
# Extension and restriction of scalars for Lie algebras and Lie modules

Lie algebras and their representations have a well-behaved theory of extension and restriction of
scalars.

## Main definitions

 * `LieAlgebra.ExtendScalars.instLieAlgebra`
 * `LieAlgebra.ExtendScalars.instLieModule`
 * `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

suppress_compilation

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A` over `R`. -/
private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A A L A M).toLinearMap

@[simp]
private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s ⊗ₜ[R] x) (t ⊗ₜ[R] m) = (s * t) ⊗ₜ ⁅x, m⁆ := rfl

instance : Bracket (A ⊗[R] L) (A ⊗[R] M) where bracket x m := bracket' R A L M x m

private theorem bracket_def (x : A ⊗[R] L) (m : A ⊗[R] M) : ⁅x, m⁆ = bracket' R A L M x m :=
  rfl

@[simp]
theorem bracket_tmul (s t : A) (x : L) (y : M) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s * t) ⊗ₜ ⁅x, y⁆ := rfl
#align lie_algebra.extend_scalars.bracket_tmul LieAlgebra.ExtendScalars.bracket_tmul

private theorem bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine' x.induction_on _ _ _
  · simp only [LinearMap.map_zero, eq_self_iff_true, LinearMap.zero_apply]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, eq_self_iff_true, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
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

private theorem bracket_leibniz_lie (x y : A ⊗[R] L) (z : A ⊗[R] M) :
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
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, map_add, LinearMap.add_apply,
      map_add, LinearMap.add_apply, h₁, h₂, add_add_add_comm]

instance instLieRing : LieRing (A ⊗[R] L) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, LinearMap.map_add]
  lie_add x y z := by simp only [bracket_def, LinearMap.map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L

instance instLieAlgebra : LieAlgebra A (A ⊗[R] L) where lie_smul _a _x _y := map_smul _ _ _
#align lie_algebra.extend_scalars.lie_algebra LieAlgebra.ExtendScalars.instLieAlgebra

instance instLieRingModule : LieRingModule (A ⊗[R] L) (A ⊗[R] M) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, LinearMap.map_add]
  lie_add x y z := by simp only [bracket_def, LinearMap.map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

instance instLieModule : LieModule A (A ⊗[R] L) (A ⊗[R] M) where
  smul_lie t x m := by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul t x m := map_smul _ _ _

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
