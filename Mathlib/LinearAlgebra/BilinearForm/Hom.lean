/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Basis

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/


open BigOperators

universe u v w

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [Ring R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {R₃ : Type*} {M₃ : Type*} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

namespace BilinForm

section ToLin'

variable [Algebra R₂ R] [Module R₂ M] [IsScalarTower R₂ R M]

/-- Auxiliary definition to define `toLinHom`; see below. -/
def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R where
  toFun y := A x y
  map_add' := A.bilin_add_right x
  map_smul' c := A.bilin_smul_right c x
#align bilin_form.to_lin_hom_aux₁ BilinForm.toLinHomAux₁

/-- Auxiliary definition to define `toLinHom`; see below. -/
def toLinHomAux₂ (A : BilinForm R M) : M →ₗ[R₂] M →ₗ[R] R where
  toFun := toLinHomAux₁ A
  map_add' x₁ x₂ :=
    LinearMap.ext fun x => by
      simp only [toLinHomAux₁, LinearMap.coe_mk, LinearMap.add_apply, add_left, AddHom.coe_mk]
  map_smul' c x :=
    LinearMap.ext <| by
      dsimp [toLinHomAux₁]
      intros
      -- Porting note: moved out of `simp only`
      rw [← algebraMap_smul R c x]
      simp only [Algebra.smul_def, LinearMap.coe_mk, LinearMap.smul_apply, smul_left]
#align bilin_form.to_lin_hom_aux₂ BilinForm.toLinHomAux₂

variable (R₂)

/-- The linear map obtained from a `BilinForm` by fixing the left co-ordinate and evaluating in
the right.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over a semiring with no particular distinguished
such subsemiring, use `toLin'`, which is `ℕ`-linear.  Over a commutative semiring, use `toLin`,
which is linear. -/
def toLinHom : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R where
  toFun := toLinHomAux₂
  map_add' A₁ A₂ :=
    LinearMap.ext fun x => by
      dsimp only [toLinHomAux₁, toLinHomAux₂]
      apply LinearMap.ext
      intro y
      simp only [toLinHomAux₂, toLinHomAux₁, LinearMap.coe_mk, LinearMap.add_apply, add_apply,
        AddHom.coe_mk]
  map_smul' c A := by
    dsimp [toLinHomAux₁, toLinHomAux₂]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [toLinHomAux₂, toLinHomAux₁, LinearMap.coe_mk, LinearMap.smul_apply, smul_apply,
      AddHom.coe_mk]
#align bilin_form.to_lin_hom BilinForm.toLinHom

variable {R₂}

@[simp]
theorem toLin'_apply (A : BilinForm R M) (x : M) : ⇑(toLinHom R₂ A x) = A x :=
  rfl
#align bilin_form.to_lin'_apply BilinForm.toLin'_apply

/-- The linear map obtained from a `BilinForm` by fixing the left co-ordinate and evaluating in
the right.
Over a commutative semiring, use `toLin`, which is linear rather than `ℕ`-linear. -/
abbrev toLin' : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  toLinHom ℕ
#align bilin_form.to_lin' BilinForm.toLin'

variable (B)

@[simp]
theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i in t, g i) w = ∑ i in t, B (g i) w :=
  (BilinForm.toLin' B).map_sum₂ t g w
#align bilin_form.sum_left BilinForm.sum_left

@[simp]
theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i in t, g i) = ∑ i in t, B w (g i) :=
  map_sum (BilinForm.toLin' B w) _ _
#align bilin_form.sum_right BilinForm.sum_right

@[simp]
theorem sum_apply {α} (t : Finset α) (B : α → BilinForm R M) (v w : M) :
    (∑ i in t, B i) v w = ∑ i in t, B i v w := by
  show coeFnAddMonoidHom (∑ i in t, B i) v w = _
  rw [map_sum, Finset.sum_apply, Finset.sum_apply]
  rfl

variable {B} (R₂)

/-- The linear map obtained from a `BilinForm` by fixing the right co-ordinate and evaluating in
the left.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over semiring with no particular distinguished
such subsemiring, use `toLin'Flip`, which is `ℕ`-linear.  Over a commutative semiring, use
`toLinFlip`, which is linear. -/
def toLinHomFlip : BilinForm R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R :=
  (toLinHom R₂).comp (flipHom R₂).toLinearMap
#align bilin_form.to_lin_hom_flip BilinForm.toLinHomFlip

variable {R₂}

@[simp]
theorem toLin'Flip_apply (A : BilinForm R M) (x : M) : ⇑(toLinHomFlip R₂ A x) = fun y => A y x :=
  rfl
#align bilin_form.to_lin'_flip_apply BilinForm.toLin'Flip_apply

/-- The linear map obtained from a `BilinForm` by fixing the right co-ordinate and evaluating in
the left.
Over a commutative semiring, use `toLinFlip`, which is linear rather than `ℕ`-linear. -/
abbrev toLin'Flip : BilinForm R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R :=
  toLinHomFlip ℕ
#align bilin_form.to_lin'_flip BilinForm.toLin'Flip

end ToLin'

end BilinForm

section EquivLin

/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `LinearMap.toBilin`.
-/
def LinearMap.toBilinAux (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂ where
  bilin x y := f x y
  bilin_add_left x y z := by
    simp only
    exact (LinearMap.map_add f x y).symm ▸ LinearMap.add_apply (f x) (f y) z
  bilin_smul_left a x y := by simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  bilin_add_right x y z := LinearMap.map_add (f x) y z
  bilin_smul_right a x y := LinearMap.map_smul (f x) a y
#align linear_map.to_bilin_aux LinearMap.toBilinAux

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def BilinForm.toLin : BilinForm R₂ M₂ ≃ₗ[R₂] M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂ :=
  { BilinForm.toLinHom R₂ with
    invFun := LinearMap.toBilinAux
    left_inv := fun B => by
      ext
      simp [LinearMap.toBilinAux]
    right_inv := fun B => by
      ext
      simp [LinearMap.toBilinAux] }
#align bilin_form.to_lin BilinForm.toLin

/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def LinearMap.toBilin : (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) ≃ₗ[R₂] BilinForm R₂ M₂ :=
  BilinForm.toLin.symm
#align linear_map.to_bilin LinearMap.toBilin

@[simp]
theorem LinearMap.toBilinAux_eq (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :
    LinearMap.toBilinAux f = LinearMap.toBilin f :=
  rfl
#align linear_map.to_bilin_aux_eq LinearMap.toBilinAux_eq

@[simp]
theorem LinearMap.toBilin_symm :
    (LinearMap.toBilin.symm : BilinForm R₂ M₂ ≃ₗ[R₂] _) = BilinForm.toLin :=
  rfl
#align linear_map.to_bilin_symm LinearMap.toBilin_symm

@[simp]
theorem BilinForm.toLin_symm :
    (BilinForm.toLin.symm : _ ≃ₗ[R₂] BilinForm R₂ M₂) = LinearMap.toBilin :=
  LinearMap.toBilin.symm_symm
#align bilin_form.to_lin_symm BilinForm.toLin_symm

@[simp, norm_cast]
theorem LinearMap.toBilin_apply (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) (x y : M₂) :
    toBilin f x y = f x y :=
  rfl

@[simp, norm_cast]
theorem BilinForm.toLin_apply (x : M₂) : ⇑(BilinForm.toLin B₂ x) = B₂ x :=
  rfl
#align bilin_form.to_lin_apply BilinForm.toLin_apply

end EquivLin

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

/-- Apply a linear map on the output of a bilinear form. -/
@[simps]
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M where
  bilin x y := f (B x y)
  bilin_add_left x y z := by simp only [BilinForm.add_left, map_add]
  bilin_smul_left r x y := by
    simp only
    rw [← smul_one_smul R r (_ : M), BilinForm.smul_left, smul_one_mul r (_ : R), map_smul,
      smul_eq_mul]
  bilin_add_right x y z := by simp only [BilinForm.add_right, map_add]
  bilin_smul_right r x y := by
    simp only
    rw [← smul_one_smul R r (_ : M), BilinForm.smul_right, smul_one_mul r (_ : R), map_smul,
      smul_eq_mul]
#align linear_map.comp_bilin_form LinearMap.compBilinForm

end LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M where
  bilin x y := B (l x) (r y)
  bilin_add_left x y z := by simp only [LinearMap.map_add, add_left]
  bilin_smul_left x y z := by simp only [LinearMap.map_smul, smul_left]
  bilin_add_right x y z := by simp only [LinearMap.map_add, add_right]
  bilin_smul_right x y z := by simp only [LinearMap.map_smul, smul_right]
#align bilin_form.comp BilinForm.comp

/-- Apply a linear map to the left argument of a bilinear form. -/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id
#align bilin_form.comp_left BilinForm.compLeft

/-- Apply a linear map to the right argument of a bilinear form. -/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f
#align bilin_form.comp_right BilinForm.compRight

theorem comp_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm R M'')
    (l r : M →ₗ[R] M') (l' r' : M' →ₗ[R] M'') :
    (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl
#align bilin_form.comp_comp BilinForm.comp_comp

@[simp]
theorem compLeft_compRight (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compLeft l).compRight r = B.comp l r :=
  rfl
#align bilin_form.comp_left_comp_right BilinForm.compLeft_compRight

@[simp]
theorem compRight_compLeft (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compRight r).compLeft l = B.comp l r :=
  rfl
#align bilin_form.comp_right_comp_left BilinForm.compRight_compLeft

@[simp]
theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl
#align bilin_form.comp_apply BilinForm.comp_apply

@[simp]
theorem compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl
#align bilin_form.comp_left_apply BilinForm.compLeft_apply

@[simp]
theorem compRight_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compRight f v w = B v (f w) :=
  rfl
#align bilin_form.comp_right_apply BilinForm.compRight_apply

@[simp]
theorem comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl
#align bilin_form.comp_id_left BilinForm.comp_id_left

@[simp]
theorem comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl
#align bilin_form.comp_id_right BilinForm.comp_id_right

@[simp]
theorem compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl
#align bilin_form.comp_left_id BilinForm.compLeft_id

@[simp]
theorem compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl
#align bilin_form.comp_right_id BilinForm.compRight_id

-- Shortcut for `comp_id_{left,right}` followed by `comp{Right,Left}_id`,
-- Needs higher priority to be applied
@[simp high]
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl
#align bilin_form.comp_id_id BilinForm.comp_id_id

theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'} (hₗ : Function.Surjective l)
    (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    cases' hₗ x with x' hx
    subst hx
    cases' hᵣ y with y' hy
    subst hy
    rw [← comp_apply, ← comp_apply, h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]
#align bilin_form.comp_inj BilinForm.comp_inj

end Comp

variable {M₂' M₂'' : Type*}

variable [AddCommMonoid M₂'] [AddCommMonoid M₂''] [Module R₂ M₂'] [Module R₂ M₂'']

section congr

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def congr (e : M₂ ≃ₗ[R₂] M₂') : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂' where
  toFun B := B.comp e.symm e.symm
  invFun B := B.comp e e
  left_inv B := ext fun x y => by simp only [comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
  right_inv B := ext fun x y => by simp only [comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply]
  map_add' B B' := ext fun x y => by simp only [comp_apply, add_apply]
  map_smul' B B' := ext fun x y => by simp [comp_apply, smul_apply]
#align bilin_form.congr BilinForm.congr

@[simp]
theorem congr_apply (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) (x y : M₂') :
    congr e B x y = B (e.symm x) (e.symm y) :=
  rfl
#align bilin_form.congr_apply BilinForm.congr_apply

@[simp]
theorem congr_symm (e : M₂ ≃ₗ[R₂] M₂') : (congr e).symm = congr e.symm := by
  ext
  simp only [congr_apply, LinearEquiv.symm_symm]
  rfl
#align bilin_form.congr_symm BilinForm.congr_symm

@[simp]
theorem congr_refl : congr (LinearEquiv.refl R₂ M₂) = LinearEquiv.refl R₂ _ :=
  LinearEquiv.ext fun _ => ext fun _ _ => rfl
#align bilin_form.congr_refl BilinForm.congr_refl

theorem congr_trans (e : M₂ ≃ₗ[R₂] M₂') (f : M₂' ≃ₗ[R₂] M₂'') :
    (congr e).trans (congr f) = congr (e.trans f) :=
  rfl
#align bilin_form.congr_trans BilinForm.congr_trans

theorem congr_congr (e : M₂' ≃ₗ[R₂] M₂'') (f : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) :
    congr e (congr f B) = congr (f.trans e) B :=
  rfl
#align bilin_form.congr_congr BilinForm.congr_congr

theorem congr_comp (e : M₂ ≃ₗ[R₂] M₂') (B : BilinForm R₂ M₂) (l r : M₂'' →ₗ[R₂] M₂') :
    (congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) l)
        (LinearMap.comp (e.symm : M₂' →ₗ[R₂] M₂) r) :=
  rfl
#align bilin_form.congr_comp BilinForm.congr_comp

theorem comp_congr (e : M₂' ≃ₗ[R₂] M₂'') (B : BilinForm R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
    congr e (B.comp l r) =
      B.comp (l.comp (e.symm : M₂'' →ₗ[R₂] M₂')) (r.comp (e.symm : M₂'' →ₗ[R₂] M₂')) :=
  rfl
#align bilin_form.comp_congr BilinForm.comp_congr

end congr

section LinMulLin

/-- `linMulLin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def linMulLin (f g : M₂ →ₗ[R₂] R₂) : BilinForm R₂ M₂ where
  bilin x y := f x * g y
  bilin_add_left x y z := by simp only [LinearMap.map_add, add_mul]
  bilin_smul_left x y z := by simp only [LinearMap.map_smul, smul_eq_mul, mul_assoc]
  bilin_add_right x y z := by simp only [LinearMap.map_add, mul_add]
  bilin_smul_right x y z := by simp only [LinearMap.map_smul, smul_eq_mul, mul_left_comm]
#align bilin_form.lin_mul_lin BilinForm.linMulLin

variable {f g : M₂ →ₗ[R₂] R₂}

@[simp]
theorem linMulLin_apply (x y) : linMulLin f g x y = f x * g y :=
  rfl
#align bilin_form.lin_mul_lin_apply BilinForm.linMulLin_apply

@[simp]
theorem linMulLin_comp (l r : M₂' →ₗ[R₂] M₂) :
    (linMulLin f g).comp l r = linMulLin (f.comp l) (g.comp r) :=
  rfl
#align bilin_form.lin_mul_lin_comp BilinForm.linMulLin_comp

@[simp]
theorem linMulLin_compLeft (l : M₂ →ₗ[R₂] M₂) :
    (linMulLin f g).compLeft l = linMulLin (f.comp l) g :=
  rfl
#align bilin_form.lin_mul_lin_comp_left BilinForm.linMulLin_compLeft

@[simp]
theorem linMulLin_compRight (r : M₂ →ₗ[R₂] M₂) :
    (linMulLin f g).compRight r = linMulLin f (g.comp r) :=
  rfl
#align bilin_form.lin_mul_lin_comp_right BilinForm.linMulLin_compRight

end LinMulLin

section Basis

variable {F₂ : BilinForm R₂ M₂}

variable {ι : Type*} (b : Basis ι R₂ M₂)

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
theorem ext_basis (h : ∀ i j, B₂ (b i) (b j) = F₂ (b i) (b j)) : B₂ = F₂ :=
  toLin.injective <| b.ext fun i => b.ext fun j => h i j
#align bilin_form.ext_basis BilinForm.ext_basis

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem sum_repr_mul_repr_mul (x y : M₂) :
    ((b.repr x).sum fun i xi => (b.repr y).sum fun j yj => xi • yj • B₂ (b i) (b j)) = B₂ x y := by
  conv_rhs => rw [← b.total_repr x, ← b.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]
#align bilin_form.sum_repr_mul_repr_mul BilinForm.sum_repr_mul_repr_mul

end Basis

end BilinForm
