/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.LinearAlgebra.Dual

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

/-- `BilinForm R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure BilinForm (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] where
  bilin : M → M → R
  bilin_add_left : ∀ x y z : M, bilin (x + y) z = bilin x z + bilin y z
  bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * bilin x y
  bilin_add_right : ∀ x y z : M, bilin x (y + z) = bilin x y + bilin x z
  bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * bilin x y
#align bilin_form BilinForm

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [Ring R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {R₃ : Type*} {M₃ : Type*} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

namespace BilinForm

instance : CoeFun (BilinForm R M) fun _ => M → M → R :=
  ⟨bilin⟩

initialize_simps_projections BilinForm (bilin → apply)

-- Porting note: removed for simpVarHead @[simp]
theorem coeFn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) : (BilinForm.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
  rfl
#align bilin_form.coe_fn_mk BilinForm.coeFn_mk

theorem coeFn_congr : ∀ {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
  | _, _, _, _, rfl, rfl => rfl
#align bilin_form.coe_fn_congr BilinForm.coeFn_congr

@[simp]
theorem add_left (x y z : M) : B (x + y) z = B x z + B y z :=
  bilin_add_left B x y z
#align bilin_form.add_left BilinForm.add_left

@[simp]
theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y :=
  bilin_smul_left B a x y
#align bilin_form.smul_left BilinForm.smul_left

@[simp]
theorem add_right (x y z : M) : B x (y + z) = B x y + B x z :=
  bilin_add_right B x y z
#align bilin_form.add_right BilinForm.add_right

@[simp]
theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y :=
  bilin_smul_right B a x y
#align bilin_form.smul_right BilinForm.smul_right

@[simp]
theorem zero_left (x : M) : B 0 x = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul]
#align bilin_form.zero_left BilinForm.zero_left

@[simp]
theorem zero_right (x : M) : B x 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), smul_right, zero_mul]
#align bilin_form.zero_right BilinForm.zero_right

@[simp]
theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_left, neg_one_mul]
#align bilin_form.neg_left BilinForm.neg_left

@[simp]
theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := by
  rw [← @neg_one_smul R₁ _ _, smul_right, neg_one_mul]
#align bilin_form.neg_right BilinForm.neg_right

@[simp]
theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]
#align bilin_form.sub_left BilinForm.sub_left

@[simp]
theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]
#align bilin_form.sub_right BilinForm.sub_right

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

-- TODO: instantiate `FunLike`
theorem coe_injective : Function.Injective ((↑) : BilinForm R M → M → M → R) := fun B D h => by
  cases B
  cases D
  congr
#align bilin_form.coe_injective BilinForm.coe_injective

@[ext]
theorem ext (H : ∀ x y : M, B x y = D x y) : B = D :=
  coe_injective <| by
    funext
    exact H _ _
#align bilin_form.ext BilinForm.ext

theorem congr_fun (h : B = D) (x y : M) : B x y = D x y :=
  h ▸ rfl
#align bilin_form.congr_fun BilinForm.congr_fun

theorem ext_iff : B = D ↔ ∀ x y, B x y = D x y :=
  ⟨congr_fun, ext⟩
#align bilin_form.ext_iff BilinForm.ext_iff

instance : Zero (BilinForm R M) where
  zero :=
    { bilin := fun _ _ => 0
      bilin_add_left := fun _ _ _ => (add_zero 0).symm
      bilin_smul_left := fun a _ _ => (mul_zero a).symm
      bilin_add_right := fun _ _ _ => (zero_add 0).symm
      bilin_smul_right := fun a _ _ => (mul_zero a).symm }

@[simp]
theorem coe_zero : ⇑(0 : BilinForm R M) = 0 :=
  rfl
#align bilin_form.coe_zero BilinForm.coe_zero

@[simp]
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl
#align bilin_form.zero_apply BilinForm.zero_apply

variable (B D B₁ D₁)

instance : Add (BilinForm R M) where
  add B D :=
    { bilin := fun x y => B x y + D x y
      bilin_add_left := fun x y z => by simp only [add_left, add_left, add_add_add_comm]
      bilin_smul_left := fun a x y => by simp only [smul_left, smul_left, mul_add]
      bilin_add_right := fun x y z => by simp only [add_right, add_right, add_add_add_comm]
      bilin_smul_right := fun a x y => by simp only [smul_right, smul_right, mul_add] }

@[simp]
theorem coe_add : ⇑(B + D) = B + D :=
  rfl
#align bilin_form.coe_add BilinForm.coe_add

@[simp]
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl
#align bilin_form.add_apply BilinForm.add_apply

/-- `BilinForm R M` inherits the scalar action by `α` on `R` if this is compatible with
multiplication.

When `R` itself is commutative, this provides an `R`-action via `Algebra.id`. -/
instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] : SMul α (BilinForm R M) where
  smul c B :=
    { bilin := fun x y => c • B x y
      bilin_add_left := fun x y z => by simp only [add_left, smul_add]
      bilin_smul_left := fun a x y => by simp only [smul_left, mul_smul_comm]
      bilin_add_right := fun x y z => by simp only [add_right, smul_add]
      bilin_smul_right := fun a x y => by simp only [smul_right, mul_smul_comm] }

@[simp]
theorem coe_smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    (B : BilinForm R M) : ⇑(a • B) = a • ⇑B :=
  rfl
#align bilin_form.coe_smul BilinForm.coe_smul

@[simp]
theorem smul_apply {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    (B : BilinForm R M) (x y : M) : (a • B) x y = a • B x y :=
  rfl
#align bilin_form.smul_apply BilinForm.smul_apply

instance {α β} [Monoid α] [Monoid β] [DistribMulAction α R] [DistribMulAction β R]
    [SMulCommClass α R R] [SMulCommClass β R R] [SMulCommClass α β R] :
    SMulCommClass α β (BilinForm R M) :=
  ⟨fun a b B => ext $ fun x y => smul_comm a b (B x y)⟩

instance {α β} [Monoid α] [Monoid β] [SMul α β] [DistribMulAction α R] [DistribMulAction β R]
    [SMulCommClass α R R] [SMulCommClass β R R] [IsScalarTower α β R] :
    IsScalarTower α β (BilinForm R M) :=
  ⟨fun a b B => ext $ fun x y => smul_assoc a b (B x y)⟩

instance {α} [Monoid α] [DistribMulAction α R] [DistribMulAction αᵐᵒᵖ R]
    [SMulCommClass α R R] [IsCentralScalar α R] :
    IsCentralScalar α (BilinForm R M) :=
  ⟨fun a B => ext $ fun x y => op_smul_eq_smul a (B x y)⟩

instance : AddCommMonoid (BilinForm R M) :=
  Function.Injective.addCommMonoid _ coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

instance : Neg (BilinForm R₁ M₁) where
  neg B :=
    { bilin := fun x y => -B x y
      bilin_add_left := fun x y z => by simp only [add_left, neg_add]
      bilin_smul_left := fun a x y => by simp only [smul_left, mul_neg]
      bilin_add_right := fun x y z => by simp only [add_right, neg_add]
      bilin_smul_right := fun a x y => by simp only [smul_right, mul_neg] }

@[simp]
theorem coe_neg : ⇑(-B₁) = -B₁ :=
  rfl
#align bilin_form.coe_neg BilinForm.coe_neg

@[simp]
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl
#align bilin_form.neg_apply BilinForm.neg_apply

instance : Sub (BilinForm R₁ M₁) where
  sub B D :=
    { bilin := fun x y => B x y - D x y
      bilin_add_left := fun x y z => by simp only [add_left, add_left, add_sub_add_comm]
      bilin_smul_left := fun a x y => by simp only [smul_left, smul_left, mul_sub]
      bilin_add_right := fun x y z => by simp only [add_right, add_right, add_sub_add_comm]
      bilin_smul_right := fun a x y => by simp only [smul_right, smul_right, mul_sub] }

@[simp]
theorem coe_sub : ⇑(B₁ - D₁) = B₁ - D₁ :=
  rfl
#align bilin_form.coe_sub BilinForm.coe_sub

@[simp]
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl
#align bilin_form.sub_apply BilinForm.sub_apply

instance : AddCommGroup (BilinForm R₁ M₁) :=
  Function.Injective.addCommGroup _ coe_injective coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance : Inhabited (BilinForm R M) :=
  ⟨0⟩

/-- `coeFn` as an `AddMonoidHom` -/
def coeFnAddMonoidHom : BilinForm R M →+ M → M → R where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add
#align bilin_form.coe_fn_add_monoid_hom BilinForm.coeFnAddMonoidHom

instance {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] :
    DistribMulAction α (BilinForm R M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance {α} [Semiring α] [Module α R] [SMulCommClass α R R] : Module α (BilinForm R M) :=
  Function.Injective.module _ coeFnAddMonoidHom coe_injective coe_smul

section flip

variable (R₂)

/-- Auxiliary construction for the flip of a bilinear form, obtained by exchanging the left and
right arguments. This version is a `LinearMap`; it is later upgraded to a `LinearEquiv`
in `flipHom`. -/
def flipHomAux [Algebra R₂ R] : BilinForm R M →ₗ[R₂] BilinForm R M where
  toFun A :=
    { bilin := fun i j => A j i
      bilin_add_left := fun x y z => A.bilin_add_right z x y
      bilin_smul_left := fun a x y => A.bilin_smul_right a y x
      bilin_add_right := fun x y z => A.bilin_add_left y z x
      bilin_smul_right := fun a x y => A.bilin_smul_left a y x }
  map_add' A₁ A₂ := by
    ext
    simp
  map_smul' c A := by
    ext
    simp
#align bilin_form.flip_hom_aux BilinForm.flipHomAux

variable {R₂}

theorem flip_flip_aux [Algebra R₂ R] (A : BilinForm R M) :
    (flipHomAux R₂) (flipHomAux R₂ A) = A := by
  ext A
  simp [flipHomAux]
#align bilin_form.flip_flip_aux BilinForm.flip_flip_aux

variable (R₂)

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. This is a
less structured version of the equiv which applies to general (noncommutative) rings `R` with a
distinguished commutative subring `R₂`; over a commutative ring use `flip`. -/
def flipHom [Algebra R₂ R] : BilinForm R M ≃ₗ[R₂] BilinForm R M :=
  { flipHomAux R₂ with
    invFun := flipHomAux R₂
    left_inv := flip_flip_aux
    right_inv := flip_flip_aux }
#align bilin_form.flip_hom BilinForm.flipHom

variable {R₂}

@[simp]
theorem flip_apply [Algebra R₂ R] (A : BilinForm R M) (x y : M) : flipHom R₂ A x y = A y x :=
  rfl
#align bilin_form.flip_apply BilinForm.flip_apply

theorem flip_flip [Algebra R₂ R] :
    (flipHom R₂).trans (flipHom R₂) = LinearEquiv.refl R₂ (BilinForm R M) := by
  ext A
  simp
#align bilin_form.flip_flip BilinForm.flip_flip

/-- The flip of a bilinear form over a ring, obtained by exchanging the left and right arguments,
here considered as an `ℕ`-linear equivalence, i.e. an additive equivalence. -/
abbrev flip' : BilinForm R M ≃ₗ[ℕ] BilinForm R M :=
  flipHom ℕ
#align bilin_form.flip' BilinForm.flip'

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbrev flip : BilinForm R₂ M₂ ≃ₗ[R₂] BilinForm R₂ M₂ :=
  flipHom R₂
#align bilin_form.flip BilinForm.flip

end flip

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

variable (R₂)

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

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0
#align bilin_form.is_ortho BilinForm.IsOrtho

theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
#align bilin_form.is_ortho_def BilinForm.isOrtho_def

theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x :=
  zero_left x
#align bilin_form.is_ortho_zero_left BilinForm.isOrtho_zero_left

theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x
#align bilin_form.is_ortho_zero_right BilinForm.isOrtho_zero_right

theorem ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : ¬B.IsOrtho x x) : x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ isOrtho_zero_left _)
#align bilin_form.ne_zero_of_not_is_ortho_self BilinForm.ne_zero_of_not_isOrtho_self

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`BilinForm.IsOrtho` -/
def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  Pairwise (B.IsOrtho on v)
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho BilinForm.iIsOrtho

theorem iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.iIsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho_def BilinForm.iIsOrtho_def

section

variable {R₄ M₄ : Type*} [Ring R₄] [IsDomain R₄]

variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[simp]
theorem isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [smul_left, mul_eq_zero, or_iff_right ha]
#align bilin_form.is_ortho_smul_left BilinForm.isOrtho_smul_left

@[simp]
theorem isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [smul_right, mul_eq_zero, or_iff_right ha]
#align bilin_form.is_ortho_smul_right BilinForm.isOrtho_smul_right

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n → V}
    (hv₁ : B.iIsOrtho v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
    have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _ hij
      rw [iIsOrtho_def.1 hv₁ _ _ hij, mul_zero]
    simp_rw [sum_left, smul_left, hsum] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this
set_option linter.uppercaseLean3 false in
#align bilin_form.linear_independent_of_is_Ortho BilinForm.linearIndependent_of_iIsOrtho

end

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

/-! ### Reflexivity, symmetry, and alternativity -/


/-- The proposition that a bilinear form is reflexive -/
def IsRefl (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = 0 → B y x = 0
#align bilin_form.is_refl BilinForm.IsRefl

namespace IsRefl

variable (H : B.IsRefl)

theorem eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y
#align bilin_form.is_refl.eq_zero BilinForm.IsRefl.eq_zero

theorem ortho_comm {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩
#align bilin_form.is_refl.ortho_comm BilinForm.IsRefl.ortho_comm

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
#align bilin_form.is_refl.neg BilinForm.IsRefl.neg

protected theorem smul {α} [Semiring α] [Module α R] [SMulCommClass α R R] [NoZeroSMulDivisors α R]
    (a : α) {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
#align bilin_form.is_refl.smul BilinForm.IsRefl.smul

protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
#align bilin_form.is_refl.group_smul BilinForm.IsRefl.groupSMul

end IsRefl

@[simp]
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl
#align bilin_form.is_refl_zero BilinForm.isRefl_zero

@[simp]
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩
#align bilin_form.is_refl_neg BilinForm.isRefl_neg

/-- The proposition that a bilinear form is symmetric -/
def IsSymm (B : BilinForm R M) : Prop :=
  ∀ x y : M, B x y = B y x
#align bilin_form.is_symm BilinForm.IsSymm

namespace IsSymm

variable (H : B.IsSymm)

protected theorem eq (x y : M) : B x y = B y x :=
  H x y
#align bilin_form.is_symm.eq BilinForm.IsSymm.eq

theorem isRefl : B.IsRefl := fun x y H1 => H x y ▸ H1
#align bilin_form.is_symm.is_refl BilinForm.IsSymm.isRefl

theorem ortho_comm {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm
#align bilin_form.is_symm.ortho_comm BilinForm.IsSymm.ortho_comm

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := fun x y => (congr_arg₂ (· + ·) (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.add BilinForm.IsSymm.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := fun x y => (congr_arg₂ Sub.sub (hB₁ x y) (hB₂ x y) : _)
#align bilin_form.is_symm.sub BilinForm.IsSymm.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := fun x y =>
  congr_arg Neg.neg (hB x y)
#align bilin_form.is_symm.neg BilinForm.IsSymm.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := fun x y =>
  congr_arg ((· • ·) a) (hB x y)
#align bilin_form.is_symm.smul BilinForm.IsSymm.smul

end IsSymm

@[simp]
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := fun _ _ => rfl
#align bilin_form.is_symm_zero BilinForm.isSymm_zero

@[simp]
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩
#align bilin_form.is_symm_neg BilinForm.isSymm_neg

variable (R₂) in
theorem isSymm_iff_flip [Algebra R₂ R] : B.IsSymm ↔ flipHom R₂ B = B :=
  (forall₂_congr fun _ _ => by exact eq_comm).trans ext_iff.symm
#align bilin_form.is_symm_iff_flip' BilinForm.isSymm_iff_flip

/-- The proposition that a bilinear form is alternating -/
def IsAlt (B : BilinForm R M) : Prop :=
  ∀ x : M, B x x = 0
#align bilin_form.is_alt BilinForm.IsAlt

namespace IsAlt

theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 :=
  H x
#align bilin_form.is_alt.self_eq_zero BilinForm.IsAlt.self_eq_zero

theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := by
  have H1 : B₁ (x + y) (x + y) = 0 := self_eq_zero H (x + y)
  rw [add_left, add_right, add_right, self_eq_zero H, self_eq_zero H, zero_add, add_zero,
    add_eq_zero_iff_neg_eq] at H1
  exact H1
#align bilin_form.is_alt.neg_eq BilinForm.IsAlt.neg_eq

theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := by
  intro x y h
  rw [← neg_eq H, h, neg_zero]
#align bilin_form.is_alt.is_refl BilinForm.IsAlt.isRefl

theorem ortho_comm (H : B₁.IsAlt) {x y : M₁} : IsOrtho B₁ x y ↔ IsOrtho B₁ y x :=
  H.isRefl.ortho_comm
#align bilin_form.is_alt.ortho_comm BilinForm.IsAlt.ortho_comm

protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) : _).trans <| add_zero _
#align bilin_form.is_alt.add BilinForm.IsAlt.add

protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
#align bilin_form.is_alt.sub BilinForm.IsAlt.sub

protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x
#align bilin_form.is_alt.neg BilinForm.IsAlt.neg

protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass α R R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg ((· • ·) a) (hB x)).trans <| smul_zero _
#align bilin_form.is_alt.smul BilinForm.IsAlt.smul

end IsAlt

@[simp]
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl
#align bilin_form.is_alt_zero BilinForm.isAlt_zero

@[simp]
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩
#align bilin_form.is_alt_neg BilinForm.isAlt_neg

/-! ### Linear adjoints -/


section LinearAdjoints

variable (B) (F : BilinForm R M)

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)
#align bilin_form.is_adjoint_pair BilinForm.IsAdjointPair

variable {B B' f f' g g'}

theorem IsAdjointPair.eq (h : IsAdjointPair B B' f g) : ∀ {x y}, B' (f x) y = B x (g y) :=
  @h
#align bilin_form.is_adjoint_pair.eq BilinForm.IsAdjointPair.eq

theorem isAdjointPair_iff_compLeft_eq_compRight (f g : Module.End R M) :
    IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g := by
  constructor <;> intro h
  · ext x
    simp only [compLeft_apply, compRight_apply]
    apply h
  · intro x y
    rw [← compLeft_apply, ← compRight_apply]
    rw [h]
#align bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right BilinForm.isAdjointPair_iff_compLeft_eq_compRight

theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun x y => by
  simp only [BilinForm.zero_left, BilinForm.zero_right, LinearMap.zero_apply]
#align bilin_form.is_adjoint_pair_zero BilinForm.isAdjointPair_zero

theorem isAdjointPair_id : IsAdjointPair B B 1 1 := fun _ _ => rfl
#align bilin_form.is_adjoint_pair_id BilinForm.isAdjointPair_id

theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']
#align bilin_form.is_adjoint_pair.add BilinForm.IsAdjointPair.add

variable {M₁' : Type*} [AddCommGroup M₁'] [Module R₁ M₁']

variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

theorem IsAdjointPair.sub (h : IsAdjointPair B₁ B₁' f₁ g₁) (h' : IsAdjointPair B₁ B₁' f₁' g₁') :
    IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']
#align bilin_form.is_adjoint_pair.sub BilinForm.IsAdjointPair.sub

variable {B₂' : BilinForm R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

theorem IsAdjointPair.smul (c : R₂) (h : IsAdjointPair B₂ B₂' f₂ g₂) :
    IsAdjointPair B₂ B₂' (c • f₂) (c • g₂) := fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]
#align bilin_form.is_adjoint_pair.smul BilinForm.IsAdjointPair.smul

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']

variable (B'' : BilinForm R M'')

theorem IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
#align bilin_form.is_adjoint_pair.comp BilinForm.IsAdjointPair.comp

theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']
#align bilin_form.is_adjoint_pair.mul BilinForm.IsAdjointPair.mul

variable (B B' B₁ B₂) (F₂ : BilinForm R₂ M₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
#align bilin_form.is_pair_self_adjoint BilinForm.IsPairSelfAdjoint

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def isPairSelfAdjointSubmodule : Submodule R₂ (Module.End R₂ M₂) where
  carrier := { f | IsPairSelfAdjoint B₂ F₂ f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
#align bilin_form.is_pair_self_adjoint_submodule BilinForm.isPairSelfAdjointSubmodule

@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ isPairSelfAdjointSubmodule B₂ F₂ ↔ IsPairSelfAdjoint B₂ F₂ f :=  by rfl
#align bilin_form.mem_is_pair_self_adjoint_submodule BilinForm.mem_isPairSelfAdjointSubmodule

theorem isPairSelfAdjoint_equiv (e : M₂' ≃ₗ[R₂] M₂) (f : Module.End R₂ M₂) :
    IsPairSelfAdjoint B₂ F₂ f ↔
      IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) := by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.compLeft f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.compRight f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M₂' →ₗ[R₂] M₂) : M₂' → M₂) := e.surjective
  show BilinForm.IsAdjointPair _ _ _ _ ↔ BilinForm.IsAdjointPair _ _ _ _
  rw [isAdjointPair_iff_compLeft_eq_compRight, isAdjointPair_iff_compLeft_eq_compRight, hᵣ,
    hₗ, comp_inj _ _ he he]
#align bilin_form.is_pair_self_adjoint_equiv BilinForm.isPairSelfAdjoint_equiv

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
#align bilin_form.is_self_adjoint BilinForm.IsSelfAdjoint

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def IsSkewAdjoint (f : Module.End R₁ M₁) :=
  IsAdjointPair B₁ B₁ f (-f)
#align bilin_form.is_skew_adjoint BilinForm.IsSkewAdjoint

theorem isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) :
    B₁.IsSkewAdjoint f ↔ IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [LinearMap.neg_apply, BilinForm.neg_apply, BilinForm.neg_right]
#align bilin_form.is_skew_adjoint_iff_neg_self_adjoint BilinForm.isSkewAdjoint_iff_neg_self_adjoint

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B₂ B₂
#align bilin_form.self_adjoint_submodule BilinForm.selfAdjointSubmodule

@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R₂ M₂) :
    f ∈ B₂.selfAdjointSubmodule ↔ B₂.IsSelfAdjoint f :=
  Iff.rfl
#align bilin_form.mem_self_adjoint_submodule BilinForm.mem_selfAdjointSubmodule

variable (B₃ : BilinForm R₃ M₃)

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B₃) B₃
#align bilin_form.skew_adjoint_submodule BilinForm.skewAdjointSubmodule

@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R₃ M₃) :
    f ∈ B₃.skewAdjointSubmodule ↔ B₃.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl
#align bilin_form.mem_skew_adjoint_submodule BilinForm.mem_skewAdjointSubmodule

end LinearAdjoints

end BilinForm

namespace BilinForm

section Orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
  carrier := { m | ∀ n ∈ N, IsOrtho B n m }
  zero_mem' x _ := isOrtho_zero_right x
  add_mem' {x y} hx hy n hn := by
    rw [IsOrtho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_add]
  smul_mem' c x hx n hn := by
    rw [IsOrtho, smul_right, show B n x = 0 from hx n hn, mul_zero]
#align bilin_form.orthogonal BilinForm.orthogonal

variable {N L : Submodule R M}

@[simp]
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m ∈ B.orthogonal N ↔ ∀ n ∈ N, IsOrtho B n m :=
  Iff.rfl
#align bilin_form.mem_orthogonal_iff BilinForm.mem_orthogonal_iff

theorem orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N := fun _ hn l hl => hn l (h hl)
#align bilin_form.orthogonal_le BilinForm.orthogonal_le

theorem le_orthogonal_orthogonal (b : B.IsRefl) : N ≤ B.orthogonal (B.orthogonal N) :=
  fun n hn _ hm => b _ _ (hm n hn)
#align bilin_form.le_orthogonal_orthogonal BilinForm.le_orthogonal_orthogonal

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ := by
  rw [← Finset.coe_singleton]
  refine' eq_bot_iff.2 fun y h => _
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  have := h.2 x ?_
  · rw [Finset.sum_singleton] at this ⊢
    suffices hμzero : μ x = 0
    · rw [hμzero, zero_smul, Submodule.mem_bot]
    change B x (μ x • x) = 0 at this
    rw [smul_right] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero hx this
  · rw [Submodule.mem_span]
    exact fun _ hp => hp <| Finset.mem_singleton_self _
#align bilin_form.span_singleton_inf_orthogonal_eq_bot BilinForm.span_singleton_inf_orthogonal_eq_bot

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (BilinForm.toLin B x) := by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [IsOrtho, smul_left, mul_eq_zero]
    exact Or.intro_right _ h
#align bilin_form.orthogonal_span_singleton_eq_to_lin_ker BilinForm.orthogonal_span_singleton_eq_toLin_ker

theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ := by
  rw [orthogonal_span_singleton_eq_toLin_ker]
  exact LinearMap.span_singleton_sup_ker_eq_top _ hx
#align bilin_form.span_singleton_sup_orthogonal_eq_top BilinForm.span_singleton_sup_orthogonal_eq_top

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }
#align bilin_form.is_compl_span_singleton_orthogonal BilinForm.isCompl_span_singleton_orthogonal

end Orthogonal

/-- The restriction of a bilinear form on a submodule. -/
@[simps apply]
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W where
  bilin a b := B a b
  bilin_add_left _ _ _ := add_left _ _ _
  bilin_smul_left _ _ _ := smul_left _ _ _
  bilin_add_right _ _ _ := add_right _ _ _
  bilin_smul_right _ _ _ := smul_right _ _ _
#align bilin_form.restrict BilinForm.restrict

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
theorem restrictSymm (B : BilinForm R M) (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := fun x y => b x y
#align bilin_form.restrict_symm BilinForm.restrictSymm

/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0
#align bilin_form.nondegenerate BilinForm.Nondegenerate

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun _ => rfl)
#align bilin_form.not_nondegenerate_zero BilinForm.not_nondegenerate_zero

end

variable {M₂' : Type*}

variable [AddCommMonoid M₂'] [Module R₂ M₂']

theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h
#align bilin_form.nondegenerate.ne_zero BilinForm.Nondegenerate.ne_zero

theorem Nondegenerate.congr {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))
#align bilin_form.nondegenerate.congr BilinForm.Nondegenerate.congr

@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R₂ M₂} (e : M₂ ≃ₗ[R₂] M₂') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩
#align bilin_form.nondegenerate_congr_iff BilinForm.nondegenerate_congr_iff

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R₂ M₂} :
    B.Nondegenerate ↔ LinearMap.ker (BilinForm.toLin B) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine' fun m hm => h _ fun x => _
    rw [← toLin_apply, hm]
    rfl
  · intro m hm
    apply h
    ext x
    exact hm x
#align bilin_form.nondegenerate_iff_ker_eq_bot BilinForm.nondegenerate_iff_ker_eq_bot

theorem Nondegenerate.ker_eq_bot {B : BilinForm R₂ M₂} (h : B.Nondegenerate) :
    LinearMap.ker (BilinForm.toLin B) = ⊥ :=
  nondegenerate_iff_ker_eq_bot.mp h
#align bilin_form.nondegenerate.ker_eq_bot BilinForm.Nondegenerate.ker_eq_bot

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `Disjoint W (B.orthogonal W)`. -/
theorem nondegenerateRestrictOfDisjointOrthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
    {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate := by
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R₁]
  refine' hW.le_bot ⟨hx, fun y hy => _⟩
  specialize b₁ ⟨y, hy⟩
  rw [restrict_apply, Submodule.coe_mk, Submodule.coe_mk] at b₁
  exact isOrtho_def.mpr (b x y b₁)
#align bilin_form.nondegenerate_restrict_of_disjoint_orthogonal BilinForm.nondegenerateRestrictOfDisjointOrthogonal

/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R]
    {B : BilinForm R M} {v : Basis n R M} (h : B.iIsOrtho v) (hB : B.Nondegenerate) (i : n) :
    ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine' v.ne_zero i (hB (v i) fun m => _)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_right]
  apply Finset.sum_eq_zero
  rintro j -
  rw [smul_right]
  convert mul_zero (vi j) using 2
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho.not_is_ortho_basis_self_of_nondegenerate BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w} [Nontrivial R]
    [NoZeroDivisors R] (B : BilinForm R M) (v : Basis n R M) (hO : B.iIsOrtho v) :
    B.Nondegenerate ↔ ∀ i, ¬B.IsOrtho (v i) (v i) := by
  refine' ⟨hO.not_isOrtho_basis_self_of_nondegenerate, fun ho m hB => _⟩
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_left, smul_left] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (ho i) hB
  · intro j _ hij
    convert mul_zero (vi j) using 2
    exact hO hij
  · intro hi
    convert zero_mul (M₀ := R) _ using 2
    exact Finsupp.not_mem_support_iff.mp hi
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho.nondegenerate_iff_not_is_ortho_basis_self BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self

section

theorem toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (B.toLin.domRestrict W).ker.map W.subtype = (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    erw [LinearMap.mem_ker] at hker
    constructor
    · simp [hx]
    · intro y _
      rw [IsOrtho, b]
      change (B.toLin.domRestrict W) ⟨x, hx⟩ y = 0
      rw [hker]
      rfl
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    refine' ⟨⟨x, hx.1⟩, _, rfl⟩
    ext y
    change B x y = 0
    rw [b]
    exact hx.2 _ Submodule.mem_top
#align bilin_form.to_lin_restrict_ker_eq_inf_orthogonal BilinForm.toLin_restrict_ker_eq_inf_orthogonal

theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) : (B.toLin.domRestrict W).range.dualCoannihilator = B.orthogonal W := by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    refine' hx (B.toLin.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw
#align bilin_form.to_lin_restrict_range_dual_coannihilator_eq_orthogonal BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal

variable [FiniteDimensional K V]

open FiniteDimensional Submodule

theorem finrank_add_finrank_orthogonal {B : BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_orthogonal _ _ b₁, ←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.toLin.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.toLin.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]
#align bilin_form.finrank_add_finrank_orthogonal BilinForm.finrank_add_finrank_orthogonal

/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_of_isCompl_orthogonal {B : BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine' Subtype.mk_eq_mk.1 (b₂ ⟨x, hx₁⟩ _)
    rintro ⟨n, hn⟩
    rw [restrict_apply, coe_mk, coe_mk, b₁]
    exact hx₂ n hn
  refine' IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V, ← this, finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add
#align bilin_form.restrict_nondegenerate_of_is_compl_orthogonal BilinForm.restrict_nondegenerate_of_isCompl_orthogonal

/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_iff_isCompl_orthogonal {B : BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) : (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => restrict_nondegenerate_of_isCompl_orthogonal b₁ b₂, fun h =>
    B.nondegenerateRestrictOfDisjointOrthogonal b₁ h.1⟩
#align bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.toLin`. -/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.toLin.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
#align bilin_form.to_dual BilinForm.toDual

theorem toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual b m n = B m n :=
  rfl
#align bilin_form.to_dual_def BilinForm.toDual_def

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  b.dualBasis.map (B.toDual hB).symm
#align bilin_form.dual_basis BilinForm.dualBasis

@[simp]
theorem dualBasis_repr_apply (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]
#align bilin_form.dual_basis_repr_apply BilinForm.dualBasis_repr_apply

theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
#align bilin_form.apply_dual_basis_left BilinForm.apply_dualBasis_left

theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym, apply_dualBasis_left]
#align bilin_form.apply_dual_basis_right BilinForm.apply_dualBasis_right

end DualBasis

end

/-! We note that we cannot use `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
theorem restrictOrthogonalSpanSingletonNondegenerate (B : BilinForm K V) (b₁ : B.Nondegenerate)
    (b₂ : B.IsRefl) {x : V} (hx : ¬B.IsOrtho x x) :
    Nondegenerate <| B.restrict <| B.orthogonal (K ∙ x) := by
  refine' fun m hm => Submodule.coe_eq_zero.1 (b₁ m.1 fun n => _)
  have : n ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩
  specialize hm ⟨z, hz⟩
  rw [restrict] at hm
  erw [add_right, show B m.1 y = 0 by rw [b₂]; exact m.2 y hy, hm, add_zero]
#align bilin_form.restrict_orthogonal_span_singleton_nondegenerate BilinForm.restrictOrthogonalSpanSingletonNondegenerate

section LinearAdjoints

theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine' eq_of_sub_eq_zero (b _ _)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
#align bilin_form.comp_left_injective BilinForm.compLeft_injective

theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
#align bilin_form.is_adjoint_pair_unique_of_nondegenerate BilinForm.isAdjointPair_unique_of_nondegenerate

variable [FiniteDimensional K V]

/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symmCompOfNondegenerate`
is the linear map `B₂.toLin⁻¹ ∘ B₁.toLin`. -/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp (BilinForm.toLin B₁)
#align bilin_form.symm_comp_of_nondegenerate BilinForm.symmCompOfNondegenerate

theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    toLin B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = toLin B₁ v := by
  erw [symmCompOfNondegenerate, LinearEquiv.apply_symm_apply (B₂.toDual b₂) _]
#align bilin_form.comp_symm_comp_of_nondegenerate_apply BilinForm.comp_symmCompOfNondegenerate_apply

@[simp]
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [← BilinForm.toLin_apply, comp_symmCompOfNondegenerate_apply]
#align bilin_form.symm_comp_of_nondegenerate_left_apply BilinForm.symmCompOfNondegenerate_left_apply

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegenerate`. -/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b
#align bilin_form.left_adjoint_of_nondegenerate BilinForm.leftAdjointOfNondegenerate

theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
#align bilin_form.is_adjoint_pair_left_adjoint_of_nondegenerate BilinForm.isAdjointPairLeftAdjointOfNondegenerate

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`BilinForm.leftAdjointOfNondegenerate`. -/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩
#align bilin_form.is_adjoint_pair_iff_eq_of_nondegenerate BilinForm.isAdjointPair_iff_eq_of_nondegenerate

end LinearAdjoints

end BilinForm
