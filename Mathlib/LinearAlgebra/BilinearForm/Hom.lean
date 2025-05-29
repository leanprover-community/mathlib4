/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## TODO

A lot of this file is now redundant following the replacement of the dedicated `_root_.BilinForm`
structure with `LinearMap.BilinForm`, which is just an alias for `M →ₗ[R] M →ₗ[R] R`. For example
`LinearMap.BilinForm.toLinHom` is now just the identity map. This redundant code should be removed.

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

open LinearMap (BilinForm)
open LinearMap (BilinMap)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

section ToLin'

/-- Auxiliary definition to define `toLinHom`; see below. -/
def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R := A x

variable (B)

theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i ∈ t, g i) w = ∑ i ∈ t, B (g i) w :=
  B.map_sum₂ t g w

variable (w : M)

theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i ∈ t, g i) = ∑ i ∈ t, B w (g i) := map_sum _ _ _

theorem sum_apply {α} (t : Finset α) (B : α → BilinForm R M) (v w : M) :
    (∑ i ∈ t, B i) v w = ∑ i ∈ t, B i v w := by
  simp only [coeFn_sum, Finset.sum_apply]

variable {B}

/-- The linear map obtained from a `BilinForm` by fixing the right co-ordinate and evaluating in
the left. -/
def toLinHomFlip : BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  flipHom.toLinearMap

theorem toLin'Flip_apply (A : BilinForm R M) (x : M) : toLinHomFlip (M := M) A x = fun y => A y x :=
  rfl

end ToLin'

end BilinForm

end LinearMap

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

/-- Apply a linear map on the output of a bilinear form. -/
@[simps!]
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M :=
  compr₂ (restrictScalars₁₂ R' R' B) f

end LinearMap

namespace LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M := B.compl₁₂ l r

/-- Apply a linear map to the left argument of a bilinear form. -/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f

theorem comp_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm R M'')
    (l r : M →ₗ[R] M') (l' r' : M' →ₗ[R] M'') :
    (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl

@[simp]
theorem compLeft_compRight (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compLeft l).compRight r = B.comp l r :=
  rfl

@[simp]
theorem compRight_compLeft (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compRight r).compLeft l = B.comp l r :=
  rfl

@[simp]
theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl

@[simp]
theorem compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

@[simp]
theorem compRight_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compRight f v w = B v (f w) :=
  rfl

@[simp]
theorem comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl

@[simp]
theorem comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl

@[simp]
theorem compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl

@[simp]
theorem compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl

-- Shortcut for `comp_id_{left,right}` followed by `comp{Right,Left}_id`,
-- Needs higher priority to be applied
@[simp high]
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl

theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'} (hₗ : Function.Surjective l)
    (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', hx⟩ := hₗ x
    subst hx
    obtain ⟨y', hy⟩ := hᵣ y
    subst hy
    rw [← comp_apply, ← comp_apply, h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

end Comp

variable {M' M'' : Type*}
variable [AddCommMonoid M'] [AddCommMonoid M''] [Module R M'] [Module R M'']

section congr

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def congr (e : M ≃ₗ[R] M') : BilinForm R M ≃ₗ[R] BilinForm R M' :=
  LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]
theorem congr_apply (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M') :
    congr e B x y = B (e.symm x) (e.symm y) :=
  rfl

@[simp]
theorem congr_symm (e : M ≃ₗ[R] M') : (congr e).symm = congr e.symm := by
  ext
  simp only [congr_apply, LinearEquiv.symm_symm]
  rfl

@[simp]
theorem congr_refl : congr (LinearEquiv.refl R M) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl

theorem congr_trans (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'') :
    (congr e).trans (congr f) = congr (e.trans f) :=
  rfl

theorem congr_congr (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M) :
    congr e (congr f B) = congr (f.trans e) B :=
  rfl

theorem congr_comp (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' →ₗ[R] M') :
    (congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M' →ₗ[R] M) l)
        (LinearMap.comp (e.symm : M' →ₗ[R] M) r) :=
  rfl

theorem comp_congr (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' →ₗ[R] M) :
    congr e (B.comp l r) =
      B.comp (l.comp (e.symm : M'' →ₗ[R] M')) (r.comp (e.symm : M'' →ₗ[R] M')) :=
  rfl

end congr

section congrRight₂

variable {N₁ N₂ N₃ : Type*}
variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
variable [Module R N₁] [Module R N₂] [Module R N₃]

/-- When `N₁` and `N₂` are equivalent, bilinear maps on `M` into `N₁` are equivalent to bilinear
maps into `N₂`. -/
def _root_.LinearEquiv.congrRight₂ (e : N₁ ≃ₗ[R] N₂) : BilinMap R M N₁ ≃ₗ[R] BilinMap R M N₂ :=
  LinearEquiv.congrRight (LinearEquiv.congrRight e)

@[simp]
theorem _root_.LinearEquiv.congrRight₂_apply (e : N₁ ≃ₗ[R] N₂) (B : BilinMap R M N₁) :
    LinearEquiv.congrRight₂ e B = compr₂ B e := rfl

@[simp]
theorem _root_.LinearEquiv.congrRight₂_refl :
    LinearEquiv.congrRight₂ (.refl R N₁) = .refl R (BilinMap R M N₁) := rfl

@[simp]
theorem _root_.LinearEquiv.congrRight_symm (e : N₁ ≃ₗ[R] N₂) :
    (LinearEquiv.congrRight₂ e (M := M)).symm = LinearEquiv.congrRight₂ e.symm :=
  rfl

theorem _root_.LinearEquiv.congrRight₂_trans (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    LinearEquiv.congrRight₂ (M := M) (e₁₂ ≪≫ₗ e₂₃) =
    LinearEquiv.congrRight₂ e₁₂ ≪≫ₗ LinearEquiv.congrRight₂ e₂₃ :=
  rfl

end congrRight₂

section LinMulLin

/-- `linMulLin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def linMulLin (f g : M →ₗ[R] R) : BilinForm R M := (LinearMap.mul R R).compl₁₂ f g

variable {f g : M →ₗ[R] R}

@[simp]
theorem linMulLin_apply (x y) : linMulLin f g x y = f x * g y :=
  rfl

@[simp]
theorem linMulLin_comp (l r : M' →ₗ[R] M) :
    (linMulLin f g).comp l r = linMulLin (f.comp l) (g.comp r) :=
  rfl

@[simp]
theorem linMulLin_compLeft (l : M →ₗ[R] M) :
    (linMulLin f g).compLeft l = linMulLin (f.comp l) g :=
  rfl

@[simp]
theorem linMulLin_compRight (r : M →ₗ[R] M) :
    (linMulLin f g).compRight r = linMulLin f (g.comp r) :=
  rfl

end LinMulLin

section Basis

variable {F₂ : BilinForm R M}
variable {ι : Type*} (b : Basis ι R M)

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
theorem ext_basis (h : ∀ i j, B (b i) (b j) = F₂ (b i) (b j)) : B = F₂ :=
  b.ext fun i => b.ext fun j => h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem sum_repr_mul_repr_mul (x y : M) :
    ((b.repr x).sum fun i xi => (b.repr y).sum fun j yj => xi • yj • B (b i) (b j)) = B x y := by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

end Basis

end BilinForm

end LinearMap
