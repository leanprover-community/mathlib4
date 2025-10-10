/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian

/-!
# Lie algebra cohomology in low degree
This file defines low degree cochains of Lie algebras with coefficients given by a module. They are
useful in the construction of central extensions, so we treat these easier cases separately from the
general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a submodule of bilinear maps, giving 2-cochains.
* `LieAlgebra.d₁₂`: The coboundary map taking 1-cochains to 2-cochains.
* `LieAlgebra.d₂₃`: A coboundary map taking 2-cochains to a space containing 3-cochains.
* `LieAlgebra.twoCocycle`: The submodule of 2-cocycles.

## TODO
* coboundaries, cohomology
* comparison to the Chevalley-Eilenberg complex.
* construction and classification of central extensions

## References
* [H. Cartan, S. Eilenberg, *Homological Algebra*](cartan-eilenberg-1956)

-/

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Lie algebra 1-cochains over `L` with coefficients in the module `M`. -/
abbrev oneCochain := L →ₗ[R] M

/-- Lie algebra 2-cochains over `L` with coefficients in the module `M`. -/
def twoCochain : Submodule R (L →ₗ[R] L →ₗ[R] M) where
  carrier := {c | ∀ x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

section

variable {R L M}

instance : FunLike (twoCochain R L M) L (L →ₗ[R] M) where
  coe := fun a x ↦ a.1 x
  coe_injective' _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (twoCochain R L M) R L (L →ₗ[R] M) where
  map_add a := a.1.map_add
  map_smulₛₗ a := a.1.map_smul

@[simp]
lemma twoCochain_alt (a : twoCochain R L M) (x : L) :
    a x x = 0 :=
  a.2 x

lemma twoCochain_skew (a : twoCochain R L M) (x y : L) : - a x y = a y x := by
  rw [neg_eq_iff_add_eq_zero, add_comm]
  simpa [map_add, twoCochain_alt a x, twoCochain_alt a y] using twoCochain_alt a (x + y)

@[simp]
lemma twoCochain_val_apply (a : twoCochain R L M) (x : L) :
    a.val x = a x :=
  rfl

@[simp]
lemma add_apply_apply (a b : twoCochain R L M) (x y : L) :
    (a + b) x y = a x y + b x y := by
  rfl


@[simp]
lemma smul_apply_apply (r : R) (a : twoCochain R L M) (x y : L) :
    (r • a) x y = r • (a x y) := by
  rfl

end

variable [LieRingModule L M] [LieModule R L M]

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
def d₁₂ : oneCochain R L M →ₗ[R] twoCochain R L M where
  toFun f :=
    { val :=
      { toFun x :=
          { toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp [smul_sub] }
        map_add' _ _ := by ext; simp; abel
        map_smul' _ _ := by ext; simp [smul_sub] }
      property x := by simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

@[simp]
lemma d₁₂_apply_apply (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆ := rfl

lemma d₁₂_apply_apply_ofTrivial [LieModule.IsTrivial L M] (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = - f ⁅x, y⁆ := by
  simp

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
private def d₂₃_aux (a : twoCochain R L M) : L →ₗ[R] L →ₗ[R] L →ₗ[R] M where
  toFun x :=
    { toFun y :=
        { toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
          map_add' _ _ := by simp; abel
          map_smul' _ _ := by abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; abel_nf; simp

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
def d₂₃ : twoCochain R L M →ₗ[R] L →ₗ[R] L →ₗ[R] L →ₗ[R] M where
  toFun := d₂₃_aux R L M
  map_add' _ _ := by ext; simp [d₂₃_aux]; abel
  map_smul' _ _ := by ext; simp [d₂₃_aux]; abel_nf; simp

@[simp]
lemma d₂₃_apply (a : twoCochain R L M) (x y z : L) :
    d₂₃ R L M a x y z =
      ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x :=
  rfl

lemma d₂₃_comp_d₁₂ : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x, leibniz_lie z x, leibniz_lie z y]
  have : a ⁅y, ⁅z, x⁆⁆ = a ⁅x, ⁅z, y⁆⁆ + a ⁅z, ⁅y, x⁆⁆ := by
    rw [congr_arg a (leibniz_lie y z x), ← lie_skew, ← lie_skew z y, lie_neg, map_add]
  simp only [lie_lie, sub_add_cancel, map_sub, ← lie_skew x y, ← lie_skew x z, ← lie_skew y z,
    lie_neg, map_neg, this]
  abel

/-- A Lie 2-cocycle is a 2-cochain that is annihilated by the coboundary map. -/
def twoCocycle : Submodule R (twoCochain R L M) := LinearMap.ker (d₂₃ R L M)

lemma mem_twoCocycle_iff (a : twoCochain R L M) : a ∈ twoCocycle R L M ↔ d₂₃ R L M a = 0 := by
  simp [twoCocycle]

lemma mem_twoCocycle_iff_of_trivial [LieModule.IsTrivial L M] (a : twoCochain R L M) :
    a ∈ twoCocycle R L M ↔
      ∀ (x y z : L), a x ⁅y, z⁆ = a ⁅x, y⁆ z + a y ⁅x, z⁆ := by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := (congrArg (fun b ↦ b x y z = 0) h).mpr rfl
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← twoCochain_skew a _ x, ← twoCochain_skew a _ y, ← this]
    abel
  · intro h
    ext x y z
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub, LinearMap.zero_apply]
    rw [← twoCochain_skew a x, ← twoCochain_skew a y, h x y z]
    abel

end LieModule.Cohomology
