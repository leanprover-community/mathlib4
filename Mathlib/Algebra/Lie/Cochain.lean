/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Abelian

/-!
# Lie algebra cohomology in low degree
This file defines low degree cochains of Lie algebras with coefficients given by a module. They are
useful in the construction of central extensions, so we treat these easier cases separately from the
general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a structure describing 2-cochains.
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
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [LieRingModule L M] [Module R M] [LieModule R L M]

/-- Lie algebra 1-cochains over `L` with coefficients in the module `M`. -/
abbrev oneCochain := L →ₗ[R] M

/-- Lie algebra 2-cochains over `L` with coefficients in the module `M`. -/
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

omit [LieRingModule L M] [LieModule R L M] in
@[simp]
lemma add_apply_apply (a b : twoCochain R L M) (x y : L) :
    (a + b) x y = a x y + b x y := by
  rfl

omit [LieRingModule L M] [LieModule R L M] in
@[simp]
lemma smul_apply_apply (r : R) (a : twoCochain R L M) (x y : L) :
    (r • a) x y = r • (a x y) := by
  rfl

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
def d₁₂ : oneCochain R L M →ₗ[R] twoCochain R L M where
  toFun f := {
    val := {
      toFun x := {
        toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp [smul_sub] }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp [smul_sub] }
    property x := by simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
@[simps]
def d₂₃ : twoCochain R L M →ₗ[R] (L →ₗ[R] L → L → M) where
  toFun a := {
    toFun x y z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp

lemma coboundary_of_coboundary : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply_apply, LinearMap.zero_apply, Pi.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x, leibniz_lie z x, leibniz_lie z y]
  have : a ⁅y, ⁅z, x⁆⁆ = a ⁅x, ⁅z, y⁆⁆ + a ⁅z, ⁅y, x⁆⁆ := by
    rw [congr_arg a (leibniz_lie y z x), ← lie_skew, ← lie_skew z y, lie_neg, map_add]
  simp only [lie_lie, sub_add_cancel, map_sub, ← lie_skew x y, ← lie_skew x z, ← lie_skew y z,
    lie_neg, map_neg, this]
  abel

end LieAlgebra
