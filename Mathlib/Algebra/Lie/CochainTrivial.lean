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

lemma twoCochain_skew (a : twoCochain R L M) (x y : L) : -a.toBilin x y = a.toBilin y x := by
  have hxy := a.alt (x + y)
  simp only [map_add, LinearMap.add_apply, a.alt x, zero_add, a.alt y, add_zero] at hxy
  exact neg_eq_of_add_eq_zero_left hxy

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
def d₂₃ : (twoCochain R L M) →ₗ[R] (L →ₗ[R] L → L → M) where
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

/-- A Lie 2-cocycle is a 2-cochain that is annihilated by the coboundary map. -/
def twoCocycle : Submodule R (twoCochain R L M) := LinearMap.ker (d₂₃ R L M)

lemma mem_twoCocycle_iff (a : twoCochain R L M) : a ∈ twoCocycle R L M ↔ (d₂₃ R L M) a = 0 := by
  simp_all [twoCocycle]

lemma mem_twoCocycle_iff_Jacobi_like (a : twoCochain R L M) :
    a ∈ twoCocycle R L M ↔
      ∀ (x y z : L), a.toBilin x ⁅y, z⁆ = a.toBilin ⁅x, y⁆ z + a.toBilin y ⁅x, z⁆ := by
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
