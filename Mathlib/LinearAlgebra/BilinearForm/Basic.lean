/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.BilinearMap

#align_import linear_algebra.bilinear_form from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

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

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

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

open BigOperators

open LinearMap (BilinForm)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

#noalign bilin_form.coe_fn_mk

theorem coeFn_congr : ∀ {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
  | _, _, _, _, rfl, rfl => rfl
#align bilin_form.coe_fn_congr LinearMap.BilinForm.coeFn_congr

theorem add_left (x y z : M) : B (x + y) z = B x z + B y z := by
  simp only [map_add, LinearMap.add_apply]
#align bilin_form.add_left LinearMap.BilinForm.add_left

theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
#align bilin_form.smul_left LinearMap.BilinForm.smul_left

theorem add_right (x y z : M) : B x (y + z) = B x y + B x z := map_add _ _ _
#align bilin_form.add_right LinearMap.BilinForm.add_right

theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y := map_smul _ _ _
#align bilin_form.smul_right LinearMap.BilinForm.smul_right

theorem zero_left (x : M) : B 0 x = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul]
#align bilin_form.zero_left LinearMap.BilinForm.zero_left

theorem zero_right (x : M) : B x 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_right, zero_mul]
#align bilin_form.zero_right LinearMap.BilinForm.zero_right

theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_left, neg_one_mul]
#align bilin_form.neg_left LinearMap.BilinForm.neg_left

theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_right, neg_one_mul]
#align bilin_form.neg_right LinearMap.BilinForm.neg_right

theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]
#align bilin_form.sub_left LinearMap.BilinForm.sub_left

theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]
#align bilin_form.sub_right LinearMap.BilinForm.sub_right

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
#align bilin_form.coe_injective LinearMap.BilinForm.coe_injective

@[ext]
theorem ext (H : ∀ x y : M, B x y = D x y) : B = D :=
  coe_injective <| by
    funext
    exact H _ _
#align bilin_form.ext LinearMap.BilinForm.ext

theorem congr_fun (h : B = D) (x y : M) : B x y = D x y :=
  h ▸ rfl
#align bilin_form.congr_fun LinearMap.BilinForm.congr_fun

theorem ext_iff : B = D ↔ ∀ x y, B x y = D x y :=
  ⟨congr_fun, ext₂⟩
#align bilin_form.ext_iff LinearMap.BilinForm.ext_iff

instance : Zero (BilinForm R M) := inferInstance

theorem coe_zero : ⇑(0 : BilinForm R M) = 0 :=
  rfl
#align bilin_form.coe_zero LinearMap.BilinForm.coe_zero

@[simp]
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl
#align bilin_form.zero_apply LinearMap.BilinForm.zero_apply

variable (B D B₁ D₁)

instance : Add (BilinForm R M) := inferInstance

theorem coe_add : ⇑(B + D) = B + D :=
  rfl
#align bilin_form.coe_add LinearMap.BilinForm.coe_add

@[simp]
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl
#align bilin_form.add_apply LinearMap.BilinForm.add_apply

/-- `BilinForm R M` inherits the scalar action by `α` on `R` if this is compatible with
multiplication.

When `R` itself is commutative, this provides an `R`-action via `Algebra.id`. -/
instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] : SMul α (BilinForm R M) :=
  inferInstance

#noalign bilin_form.coe_smul
#noalign bilin_form.smul_apply

instance {α β} [Monoid α] [Monoid β] [DistribMulAction α R] [DistribMulAction β R]
    [SMulCommClass R α R] [SMulCommClass R β R] [SMulCommClass α β R] :
    SMulCommClass α β (BilinForm R M) := inferInstance

instance {α β} [Monoid α] [Monoid β] [SMul α β] [DistribMulAction α R] [DistribMulAction β R]
    [SMulCommClass R α R] [SMulCommClass R β R] [IsScalarTower α β R] :
    IsScalarTower α β (BilinForm R M) := inferInstance

instance {α} [Monoid α] [DistribMulAction α R] [DistribMulAction αᵐᵒᵖ R]
    [SMulCommClass R α R] [IsCentralScalar α R] :
    IsCentralScalar α (BilinForm R M) := inferInstance

instance : AddCommMonoid (BilinForm R M) := inferInstance

instance : Neg (BilinForm R₁ M₁) := inferInstance

theorem coe_neg : ⇑(-B₁) = -B₁ :=
  rfl
#align bilin_form.coe_neg LinearMap.BilinForm.coe_neg

@[simp]
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl
#align bilin_form.neg_apply LinearMap.BilinForm.neg_apply

instance : Sub (BilinForm R₁ M₁) := inferInstance

theorem coe_sub : ⇑(B₁ - D₁) = B₁ - D₁ :=
  rfl
#align bilin_form.coe_sub LinearMap.BilinForm.coe_sub

@[simp]
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl
#align bilin_form.sub_apply LinearMap.BilinForm.sub_apply

instance : AddCommGroup (BilinForm R₁ M₁) := inferInstance

instance : Inhabited (BilinForm R M) := inferInstance

/-- `coeFn` as an `AddMonoidHom` -/
def coeFnAddMonoidHom : BilinForm R M →+ M → M → R where
  toFun := (fun B x y => B x y)
  map_zero' := rfl
  map_add' _ _ := rfl
#align bilin_form.coe_fn_add_monoid_hom LinearMap.BilinForm.coeFnAddMonoidHom

instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] :
    DistribMulAction α (BilinForm R M) := inferInstance

instance {α} [CommSemiring α] [Module α R] [SMulCommClass R α R] : Module α (BilinForm R M) :=
  inferInstance

section flip

/-- Auxiliary construction for the flip of a bilinear form, obtained by exchanging the left and
right arguments. This version is a `LinearMap`; it is later upgraded to a `LinearEquiv`
in `flipHom`. -/
def flipHomAux : (BilinForm R M) →ₗ[R] (BilinForm R M) where
  toFun A := A.flip
  map_add' A₁ A₂ := by
    ext
    simp only [LinearMap.flip_apply, LinearMap.add_apply]
  map_smul' c A := by
    ext
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, RingHom.id_apply]
#align bilin_form.flip_hom_aux LinearMap.BilinForm.flipHomAux

theorem flip_flip_aux (A : BilinForm R M) :
    flipHomAux (M := M) (flipHomAux (M := M) A) = A := by
  ext A
  simp [flipHomAux]
#align bilin_form.flip_flip_aux LinearMap.BilinForm.flip_flip_aux

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. -/
def flipHom : BilinForm R M ≃ₗ[R] BilinForm R M :=
  { flipHomAux with
    invFun := flipHomAux (M := M)
    left_inv := flip_flip_aux
    right_inv := flip_flip_aux }
#align bilin_form.flip_hom LinearMap.BilinForm.flipHom

@[simp]
theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
  rfl
#align bilin_form.flip_apply LinearMap.BilinForm.flip_apply

theorem flip_flip :
    flipHom.trans flipHom = LinearEquiv.refl R (BilinForm R M) := by
  ext A
  simp
#align bilin_form.flip_flip LinearMap.BilinForm.flip_flip

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbrev flip : BilinForm R M ≃ₗ[R] BilinForm R M :=
  flipHom
#align bilin_form.flip LinearMap.BilinForm.flip

end flip

/-- The restriction of a bilinear form on a submodule. -/
@[simps! apply]
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W :=
  LinearMap.domRestrict₁₂ B W W
#align bilin_form.restrict LinearMap.BilinForm.restrict

end BilinForm

end LinearMap
