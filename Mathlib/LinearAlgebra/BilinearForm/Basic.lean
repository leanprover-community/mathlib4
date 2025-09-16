/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an `R`-(semi)module `M`, is a function from `M × M` to `R`,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `QuadraticForm.lean` with
`exists_orthogonal_basis`.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

export LinearMap (BilinForm)

open LinearMap (BilinForm)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

theorem add_left (x y z : M) : B (x + y) z = B x z + B y z := map_add₂ _ _ _ _

theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y := map_smul₂ _ _ _ _

theorem add_right (x y z : M) : B x (y + z) = B x y + B x z := map_add _ _ _

theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y := map_smul _ _ _

theorem zero_left (x : M) : B 0 x = 0 := map_zero₂ _ _

theorem zero_right (x : M) : B x 0 = 0 := map_zero _

theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := map_neg₂ _ _ _

theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := map_neg _ _

theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := map_sub₂ _ _ _ _

theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := map_sub _ _ _

lemma smul_left_of_tower (r : S) (x y : M) : B (r • x) y = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r, smul_left, Algebra.smul_def]

lemma smul_right_of_tower (r : S) (x y : M) : B x (r • y) = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r, smul_right, Algebra.smul_def]

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

-- TODO: instantiate `FunLike`
theorem coe_injective : Function.Injective ((fun B x y => B x y) : BilinForm R M → M → M → R) :=
  fun B D h => by
    ext x y
    apply congrFun₂ h

@[ext]
theorem ext (H : ∀ x y : M, B x y = D x y) : B = D := ext₂ H

theorem congr_fun (h : B = D) (x y : M) : B x y = D x y := congr_fun₂ h _ _

@[simp]
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl

variable (B D B₁ D₁)

@[simp]
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl

@[simp]
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl

@[simp]
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl

/-- `coeFn` as an `AddMonoidHom` -/
@[simps]
def coeFnAddMonoidHom : BilinForm R M →+ M → M → R where
  toFun := fun B x y => B x y
  map_zero' := rfl
  map_add' _ _ := rfl

section flip

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. -/
def flipHom : BilinForm R M ≃ₗ[R] BilinForm R M := LinearMap.lflip

@[simp]
theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
  rfl

theorem flip_flip :
    flipHom.trans flipHom = LinearEquiv.refl R (BilinForm R M) := by
  ext A
  simp

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbrev flip (B : BilinForm R M) :=
  flipHom B

end flip

/-- The restriction of a bilinear form on a submodule. -/
@[simps! apply]
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W :=
  LinearMap.domRestrict₁₂ B W W

end BilinForm

@[simp]
theorem lsmul_flip_apply (m : M) : (lsmul R M).flip m = toSpanSingleton R M m := rfl

end LinearMap
