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
def twoCochain : Submodule R (L →ₗ[R] L →ₗ[R] M) where
  carrier := {c | ∀ x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

instance : FunLike (twoCochain R L M) L (L →ₗ[R] M) where
  coe := fun a x ↦ a.1 x
  coe_injective' _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (twoCochain R L M) R L (L →ₗ[R] M) where
  map_add a := a.1.map_add
  map_smulₛₗ a := a.1.map_smul

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
def d₁₂ : oneCochain R L M →ₗ[R] twoCochain R L M where
  toFun f := {
    val := {
      toFun x := f ∘ₗ LieModule.toEnd R L L x
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
    property x := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
@[simps]
def d₂₃ : twoCochain R L M →ₗ[R] (L →ₗ[R] L → L → M) where
  toFun a := {
    toFun x y z := a.1 x ⁅y, z⁆ + a.1 y ⁅z, x⁆ + a.1 z ⁅x, y⁆
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp

lemma coboundary_of_coboundary : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, d₂₃_apply_apply, d₁₂_apply_coe_apply,
    LieModule.toEnd_apply_apply, LinearMap.zero_apply, Pi.ofNat_apply]
  rw [← LinearMap.map_add, ← LinearMap.map_add, lie_jacobi, map_zero]

end LieAlgebra
