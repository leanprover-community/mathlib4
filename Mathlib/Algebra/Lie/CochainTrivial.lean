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

def twoCochain : Submodule R (L →ₗ[R] L →ₗ[R] M) where
  carrier := {c | ∀ x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

instance : FunLike (twoCochain R L M) L (L →ₗ[R] M) where
  coe := fun a x ↦ a.val x
  coe_injective' _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (twoCochain R L M) R L (L →ₗ[R] M) where
  map_add a := a.val.map_add
  map_smulₛₗ a := a.val.map_smul

lemma twoCochain_skew (a : twoCochain R L M) (x y : L) : -a.val x y = a.val y x := by
  have hxy := a.2 (x + y)
  simp only [map_add, LinearMap.add_apply, a.2 x, zero_add, a.2 y, add_zero] at hxy
  exact neg_eq_of_add_eq_zero_left hxy

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
def d₂₃ : (twoCochain R L M) →ₗ[R] (L →ₗ[R] L → L → M) where
  toFun a := {
    toFun x y z := a.val x ⁅y, z⁆ + a.val y ⁅z, x⁆ + a.val z ⁅x, y⁆
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp

lemma coboundary_of_coboundary : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, d₂₃_apply_apply, d₁₂_apply_coe_apply,
    LieModule.toEnd_apply_apply, LinearMap.zero_apply, Pi.zero_apply]
  rw [← LinearMap.map_add, ← LinearMap.map_add, lie_jacobi, map_zero]

/-- A Lie 2-cocycle is a 2-cochain that is annihilated by the coboundary map. -/
def twoCocycle : Submodule R (twoCochain R L M) := LinearMap.ker (d₂₃ R L M)

lemma mem_twoCocycle_iff (a : twoCochain R L M) : a ∈ twoCocycle R L M ↔ (d₂₃ R L M) a = 0 := by
  simp_all [twoCocycle]

lemma mem_twoCocycle_iff_Jacobi_like (a : twoCochain R L M) :
    a ∈ twoCocycle R L M ↔
      ∀ (x y z : L), a.val x ⁅y, z⁆ = a.val ⁅x, y⁆ z + a.val y ⁅x, z⁆ := by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := by simp [h]
    rw [d₂₃_apply_apply, add_eq_zero_iff_neg_eq] at this
    rw [← twoCochain_skew R L M _ z, (lie_skew x z).symm, LinearMap.map_neg, ← this]
    simp
  · intro h
    rw [mem_twoCocycle_iff]
    ext x y z
    have := h x y z
    rw [← twoCochain_skew R L M _ z, (lie_skew x z).symm, map_neg] at this
    simp [this]

/-- A Lie 2-coboundary is a 2-cochain that lies in the image of the coboundary map. -/
def twoCoboundary : Submodule R (twoCochain R L M) := LinearMap.range (d₁₂ R L M)

/-- superfluous? -/
def coboundaryMap : oneCochain R L M →ₗ[R] twoCoboundary R L M := (d₁₂ R L M).rangeRestrict

lemma twoCoboundary_le_twoCocycle : (twoCoboundary R L M) ≤ (twoCocycle R L M) := by
  intro _ h
  obtain ⟨b, hb⟩ := h
  have := coboundary_of_coboundary R L M
  rw [LinearMap.ext_iff] at this
  simpa [mem_twoCocycle_iff, ← hb] using this b

/-- Degree 2 cohomology `H²(L,M)` is the quotient of 2-cocycles by 2-coboundaries. -/
def twoCohomology := (twoCocycle R L M) ⧸ (twoCoboundary R L M).submoduleOf (twoCocycle R L M)

/-- Degree 2 cohomology `H²(L,M)` is an additive commutative group. -/
instance : AddCommGroup (twoCohomology R L M) :=
  Submodule.Quotient.addCommGroup _

/-- Degree 2 cohomology `H²(L,M)` is a module over the scalar ring `R`. -/
instance : Module R (twoCohomology R L M) :=
  Submodule.Quotient.module' _

end LieAlgebra
