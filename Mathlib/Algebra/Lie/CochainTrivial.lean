/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Lie algebra cohomology in low degree with trivial coefficients
This file defines low degree cochains of Lie algebras with coefficients given by a
module with trivial action. They are useful in the construction of central extensions, so we
treat these easier cases separately from the general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a structure describing 2-cochains where the coefficients take trivial
  action.
* `LieAlgebra.d₁₂`: The coboundary map taking 1-cochains to 2-cochains.
* `LieAlgebra.d₂₃`: A coboundary map taking 2-cochains to a space containing 3-cochains.

## TODO
* cocycles, cohomology
* comparison to the Chevalley-Eilenberg complex.
* construction and classification of central extensions

## References
* [H. Cartan, S. Eilenberg, *Homological Algebra*](cartan-eilenberg-1956)

-/

namespace LieAlgebra

variable (R : Type*) [CommRing R]
variable (L M : Type*) [LieRing L] [AddCommGroup M] [LieAlgebra R L] [Module R M]

/-- Lie algebra 1-cochains over `L` with coefficients in the trivial module `M`. -/
abbrev oneCochain := L →ₗ[R] M

/-- Lie algebra 2-cochains over `L` with coefficients in the trivial module `M`. -/
@[ext] structure twoCochain where
  /-- The underlying bilinear map for a 2-cochain. -/
  toBilin : L →ₗ[R] L →ₗ[R] M
  alt x : toBilin x x = 0

instance : FunLike (twoCochain R L M) L (L →ₗ[R] M) where
  coe := fun a x ↦ twoCochain.toBilin a x
  coe_injective' _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (twoCochain R L M) R L (L →ₗ[R] M) where
  map_add a := (twoCochain.toBilin a).map_add
  map_smulₛₗ a := (twoCochain.toBilin a).map_smul

instance : Zero (twoCochain R L M) where
  zero := {
    toBilin := {
      toFun a := 0
      map_add' x y := by simp
      map_smul' r x := by simp }
    alt x := by simp }

@[simp] lemma toBilin_zero : (0 : twoCochain R L M).toBilin = 0 := rfl

instance : Add (twoCochain R L M) where
  add a b := {
    toBilin := a.toBilin + b.toBilin
    alt x := by simp [a.alt, b.alt] }

@[simp] lemma toBilin_add (a b : twoCochain R L M) : (a + b).toBilin = a.toBilin + b.toBilin := rfl

instance : SMul R (twoCochain R L M) where
  smul r a := {
    toBilin := r • a.toBilin
    alt := fun _ ↦ by simp [a.alt] }

@[simp] lemma toBilin_smul (r : R) (a : twoCochain R L M) : (r • a).toBilin = r • a.toBilin := rfl

instance : AddCommGroup (twoCochain R L M) where
  add_assoc _ _ _ := by ext; simp [add_assoc]
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp
  nsmul n a := (n : R) • a
  nsmul_zero _ := by ext; simp
  nsmul_succ _ _ := by ext; simp [add_smul]
  neg a := (-1 : R) • a
  zsmul n a := (n : R) • a
  zsmul_zero' _ := by ext; simp
  zsmul_succ' _ _ := by ext; simp [add_smul]
  zsmul_neg' _ _ := by ext; simp [add_smul, add_comm]
  neg_add_cancel _ := by ext; simp
  add_comm _ _ := by ext; simp [add_comm]

instance : Module R (twoCochain R L M) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
def d₁₂ : oneCochain R L M →ₗ[R] twoCochain R L M where
  toFun f := {
    toBilin := {
      toFun x := f ∘ₗ LieAlgebra.bracketLinear R L L x
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    alt x := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
@[simps]
def d₂₃ : twoCochain R L M →ₗ[R] (L →ₗ[R] L → L → M) where
  toFun a := {
    toFun x y z := a.toBilin x ⁅y, z⁆ + a.toBilin y ⁅z, x⁆ + a.toBilin z ⁅x, y⁆
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp

lemma coboundary_of_coboundary : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, d₂₃_apply_apply, d₁₂_apply_toBilin_apply,
    bracketLinear_apply_apply, LinearMap.zero_apply, Pi.zero_apply, ← LinearMap.map_add, lie_jacobi,
    map_zero]

end LieAlgebra
