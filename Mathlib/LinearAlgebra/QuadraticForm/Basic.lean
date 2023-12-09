/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric

#align_import linear_algebra.quadratic_form.basic from "leanprover-community/mathlib"@"11b92770e4d49ff3982504c4dab918ac0887fe33"

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form on a ring `R` is a map `Q : M → R` such that:
* `QuadraticForm.map_smul`: `Q (a • x) = a * a * Q x`
* `QuadraticForm.polar_add_left`, `QuadraticForm.polar_add_right`,
  `QuadraticForm.polar_smul_left`, `QuadraticForm.polar_smul_right`:
  the map `QuadraticForm.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to semirings using the approach in [izhakian2016][] which requires that
there be a (possibly non-unique) companion bilinear form `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `QuadraticForm.polar Q`.

To build a `QuadraticForm` from the `polar` axioms, use `QuadraticForm.ofPolar`.

Quadratic forms come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `QuadraticForm.ofPolar`: a more familiar constructor that works on rings
 * `QuadraticForm.associated`: associated bilinear form
 * `QuadraticForm.PosDef`: positive definite quadratic forms
 * `QuadraticForm.Anisotropic`: anisotropic quadratic forms
 * `QuadraticForm.discr`: discriminant of a quadratic form

## Main statements

 * `QuadraticForm.associated_left_inverse`,
 * `QuadraticForm.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms
 * `BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear form `B`.

## Notation

In this file, the variable `R` is used when a `Ring` structure is sufficient and
`R₁` is used when specifically a `CommRing` is required. This allows us to keep
`[Module R M]` and `[Module R₁ M]` assumptions in the variables without
confusion between `*` from `Ring` and `*` from `CommRing`.

The variable `S` is used when `R` itself has a `•` action.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/


universe u v w

variable {S T : Type*}

variable {R R₁ : Type*} {M : Type*}

open BigOperators

section Polar

variable [Ring R] [CommRing R₁] [AddCommGroup M]

namespace QuadraticForm

/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
  f (x + y) - f x - f y
#align quadratic_form.polar QuadraticForm.polar

theorem polar_add (f g : M → R) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel
#align quadratic_form.polar_add QuadraticForm.polar_add

theorem polar_neg (f : M → R) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]
#align quadratic_form.polar_neg QuadraticForm.polar_neg

theorem polar_smul [Monoid S] [DistribMulAction S R] (f : M → R) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]
#align quadratic_form.polar_smul QuadraticForm.polar_smul

theorem polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]
#align quadratic_form.polar_comm QuadraticForm.polar_comm

/-- Auxiliary lemma to express bilinearity of `QuadraticForm.polar` without subtraction. -/
theorem polar_add_left_iff {f : M → R} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) := by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj]
#align quadratic_form.polar_add_left_iff QuadraticForm.polar_add_left_iff

theorem polar_comp {F : Type*} [Ring S] [AddMonoidHomClass F R S] (f : M → R) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Pi.smul_apply, Function.comp_apply, map_sub]
#align quadratic_form.polar_comp QuadraticForm.polar_comp

end QuadraticForm

end Polar

/-- A quadratic form over a module.

For a more familiar constructor when `R` is a ring, see `QuadraticForm.ofPolar`. -/
structure QuadraticForm (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] where
  toFun : M → R
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = a * a * toFun x
  exists_companion' : ∃ B : BilinForm R M, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y
#align quadratic_form QuadraticForm

namespace QuadraticForm

section FunLike

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {Q Q' : QuadraticForm R M}

instance funLike : FunLike (QuadraticForm R M) M fun _ => R where
  coe := toFun
  coe_injective' x y h := by cases x; cases y; congr
#align quadratic_form.fun_like QuadraticForm.funLike

/-- Helper instance for when there's too many metavariables to apply
`FunLike.hasCoeToFun` directly. -/
instance : CoeFun (QuadraticForm R M) fun _ => M → R :=
  ⟨FunLike.coe⟩

variable (Q)

/-- The `simp` normal form for a quadratic form is `FunLike.coe`, not `toFun`. -/
@[simp]
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl
#align quadratic_form.to_fun_eq_coe QuadraticForm.toFun_eq_coe

-- this must come after the coe_to_fun definition
initialize_simps_projections QuadraticForm (toFun → apply)

variable {Q}

@[ext]
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  FunLike.ext _ _ H
#align quadratic_form.ext QuadraticForm.ext

theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  FunLike.congr_fun h _
#align quadratic_form.congr_fun QuadraticForm.congr_fun

theorem ext_iff : Q = Q' ↔ ∀ x, Q x = Q' x :=
  FunLike.ext_iff
#align quadratic_form.ext_iff QuadraticForm.ext_iff

/-- Copy of a `QuadraticForm` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (Q : QuadraticForm R M) (Q' : M → R) (h : Q' = ⇑Q) : QuadraticForm R M where
  toFun := Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'
#align quadratic_form.copy QuadraticForm.copy

@[simp]
theorem coe_copy (Q : QuadraticForm R M) (Q' : M → R) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' :=
  rfl
#align quadratic_form.coe_copy QuadraticForm.coe_copy

theorem copy_eq (Q : QuadraticForm R M) (Q' : M → R) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
  FunLike.ext' h
#align quadratic_form.copy_eq QuadraticForm.copy_eq

end FunLike

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (Q : QuadraticForm R M)

theorem map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x :=
  Q.toFun_smul a x
#align quadratic_form.map_smul QuadraticForm.map_smul

theorem exists_companion : ∃ B : BilinForm R M, ∀ x y, Q (x + y) = Q x + Q y + B x y :=
  Q.exists_companion'
#align quadratic_form.exists_companion QuadraticForm.exists_companion

theorem map_add_add_add_map (x y z : M) :
    Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) := by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp [h]
  abel
#align quadratic_form.map_add_add_add_map QuadraticForm.map_add_add_add_map

theorem map_add_self (x : M) : Q (x + x) = 4 * Q x := by
  rw [← one_smul R x, ← add_smul, map_smul]
  norm_num
#align quadratic_form.map_add_self QuadraticForm.map_add_self

-- porting note: removed @[simp] because it is superseded by `ZeroHomClass.map_zero`
theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]
#align quadratic_form.map_zero QuadraticForm.map_zero

instance zeroHomClass : ZeroHomClass (QuadraticForm R M) M R :=
  { QuadraticForm.funLike with map_zero := map_zero }
#align quadratic_form.zero_hom_class QuadraticForm.zeroHomClass

theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x, map_smul, ← RingHom.map_mul, Algebra.smul_def]
#align quadratic_form.map_smul_of_tower QuadraticForm.map_smul_of_tower

end Semiring

section Ring

variable [Ring R] [CommRing R₁] [AddCommGroup M]

variable [Module R M] (Q : QuadraticForm R M)

@[simp]
theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_mul]
#align quadratic_form.map_neg QuadraticForm.map_neg

theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by rw [← neg_sub, map_neg]
#align quadratic_form.map_sub QuadraticForm.map_sub

@[simp]
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_add, QuadraticForm.map_zero, sub_zero, sub_self]
#align quadratic_form.polar_zero_left QuadraticForm.polar_zero_left

@[simp]
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
  polar_add_left_iff.mpr <| Q.map_add_add_add_map x x' y
#align quadratic_form.polar_add_left QuadraticForm.polar_add_left

@[simp]
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a * polar Q x y := by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, BilinForm.smul_left, sub_sub, add_sub_cancel']
#align quadratic_form.polar_smul_left QuadraticForm.polar_smul_left

@[simp]
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x, polar_smul_left, neg_one_mul]
#align quadratic_form.polar_neg_left QuadraticForm.polar_neg_left

@[simp]
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]
#align quadratic_form.polar_sub_left QuadraticForm.polar_sub_left

@[simp]
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zero, polar, QuadraticForm.map_zero, sub_self]
#align quadratic_form.polar_zero_right QuadraticForm.polar_zero_right

@[simp]
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]
#align quadratic_form.polar_add_right QuadraticForm.polar_add_right

@[simp]
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a * polar Q x y := by
  rw [polar_comm Q x, polar_comm Q x, polar_smul_left]
#align quadratic_form.polar_smul_right QuadraticForm.polar_smul_right

@[simp]
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y, polar_smul_right, neg_one_mul]
#align quadratic_form.polar_neg_right QuadraticForm.polar_neg_right

@[simp]
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]
#align quadratic_form.polar_sub_right QuadraticForm.polar_sub_right

@[simp]
theorem polar_self (x : M) : polar Q x x = 2 * Q x := by
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ← two_mul, ← two_mul, ← mul_assoc]
  norm_num
#align quadratic_form.polar_self QuadraticForm.polar_self

/-- `QuadraticForm.polar` as a bilinear form -/
@[simps]
def polarBilin : BilinForm R M where
  bilin := polar Q
  bilin_add_left := polar_add_left Q
  bilin_smul_left := polar_smul_left Q
  bilin_add_right x y z := by simp_rw [polar_comm _ x, polar_add_left Q]
  bilin_smul_right r x y := by simp_rw [polar_comm _ x, polar_smul_left Q]
#align quadratic_form.polar_bilin QuadraticForm.polarBilin

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x, polar_smul_left, Algebra.smul_def]
#align quadratic_form.polar_smul_left_of_tower QuadraticForm.polar_smul_left_of_tower

@[simp]
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a y, polar_smul_right, Algebra.smul_def]
#align quadratic_form.polar_smul_right_of_tower QuadraticForm.polar_smul_right_of_tower

/-- An alternative constructor to `QuadraticForm.mk`, for rings where `polar` can be used. -/
@[simps]
def ofPolar (toFun : M → R) (toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = a * a * toFun x)
    (polar_add_left : ∀ x x' y : M, polar toFun (x + x') y = polar toFun x y + polar toFun x' y)
    (polar_smul_left : ∀ (a : R) (x y : M), polar toFun (a • x) y = a • polar toFun x y) :
    QuadraticForm R M :=
  { toFun
    toFun_smul
    exists_companion' :=
      ⟨{  bilin := polar toFun
          bilin_add_left := polar_add_left
          bilin_smul_left := polar_smul_left
          bilin_add_right := fun x y z => by simp_rw [polar_comm _ x, polar_add_left]
          bilin_smul_right := fun r x y => by
            simp_rw [polar_comm _ x, polar_smul_left, smul_eq_mul] },
        fun x y => by rw [BilinForm.coeFn_mk, polar, sub_sub, add_sub_cancel'_right]⟩ }
#align quadratic_form.of_polar QuadraticForm.ofPolar

/-- In a ring the companion bilinear form is unique and equal to `QuadraticForm.polar`. -/
theorem choose_exists_companion : Q.exists_companion.choose = polarBilin Q :=
  BilinForm.ext fun x y => by
    rw [polarBilin_apply, polar, Q.exists_companion.choose_spec, sub_sub, add_sub_cancel']
#align quadratic_form.some_exists_companion QuadraticForm.choose_exists_companion

end Ring

section SemiringOperators

variable [Semiring R] [AddCommMonoid M] [Module R M]

section SMul

variable [Monoid S] [Monoid T] [DistribMulAction S R] [DistribMulAction T R]
variable [SMulCommClass S R R] [SMulCommClass T R R]

/-- `QuadraticForm R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `Algebra.id`. -/
instance : SMul S (QuadraticForm R M) :=
  ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by rw [Pi.smul_apply, map_smul, Pi.smul_apply, mul_smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨a • B, by simp [h]⟩ }⟩

@[simp]
theorem coeFn_smul (a : S) (Q : QuadraticForm R M) : ⇑(a • Q) = a • ⇑Q :=
  rfl
#align quadratic_form.coe_fn_smul QuadraticForm.coeFn_smul

@[simp]
theorem smul_apply (a : S) (Q : QuadraticForm R M) (x : M) : (a • Q) x = a • Q x :=
  rfl
#align quadratic_form.smul_apply QuadraticForm.smul_apply

instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticForm R M) where
  smul_comm _s _t _q := ext <| fun _ => smul_comm _ _ _

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticForm R M) where
  smul_assoc _s _t _q := ext <| fun _ => smul_assoc _ _ _

end SMul

instance : Zero (QuadraticForm R M) :=
  ⟨{  toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [mul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, BilinForm.zero_apply]⟩ }⟩

@[simp]
theorem coeFn_zero : ⇑(0 : QuadraticForm R M) = 0 :=
  rfl
#align quadratic_form.coe_fn_zero QuadraticForm.coeFn_zero

@[simp]
theorem zero_apply (x : M) : (0 : QuadraticForm R M) x = 0 :=
  rfl
#align quadratic_form.zero_apply QuadraticForm.zero_apply

instance : Inhabited (QuadraticForm R M) :=
  ⟨0⟩

instance : Add (QuadraticForm R M) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, map_smul, mul_add]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_apply, h, h', BilinForm.add_apply, add_add_add_comm]⟩ }⟩

@[simp]
theorem coeFn_add (Q Q' : QuadraticForm R M) : ⇑(Q + Q') = Q + Q' :=
  rfl
#align quadratic_form.coe_fn_add QuadraticForm.coeFn_add

@[simp]
theorem add_apply (Q Q' : QuadraticForm R M) (x : M) : (Q + Q') x = Q x + Q' x :=
  rfl
#align quadratic_form.add_apply QuadraticForm.add_apply

instance : AddCommMonoid (QuadraticForm R M) :=
  FunLike.coe_injective.addCommMonoid _ coeFn_zero coeFn_add fun _ _ => coeFn_smul _ _

/-- `@CoeFn (QuadraticForm R M)` as an `AddMonoidHom`.

This API mirrors `AddMonoidHom.coeFn`. -/
@[simps apply]
def coeFnAddMonoidHom : QuadraticForm R M →+ M → R where
  toFun := FunLike.coe
  map_zero' := coeFn_zero
  map_add' := coeFn_add
#align quadratic_form.coe_fn_add_monoid_hom QuadraticForm.coeFnAddMonoidHom

/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps! apply]
def evalAddMonoidHom (m : M) : QuadraticForm R M →+ R :=
  (Pi.evalAddMonoidHom _ m).comp coeFnAddMonoidHom
#align quadratic_form.eval_add_monoid_hom QuadraticForm.evalAddMonoidHom

section Sum

@[simp]
theorem coeFn_sum {ι : Type*} (Q : ι → QuadraticForm R M) (s : Finset ι) :
    ⇑(∑ i in s, Q i) = ∑ i in s, ⇑(Q i) :=
  (coeFnAddMonoidHom : QuadraticForm R M →+ M → R).map_sum Q s
#align quadratic_form.coe_fn_sum QuadraticForm.coeFn_sum

@[simp]
theorem sum_apply {ι : Type*} (Q : ι → QuadraticForm R M) (s : Finset ι) (x : M) :
    (∑ i in s, Q i) x = ∑ i in s, Q i x :=
  (evalAddMonoidHom x : _ →+ R).map_sum Q s
#align quadratic_form.sum_apply QuadraticForm.sum_apply

end Sum

instance [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] :
    DistribMulAction S (QuadraticForm R M) where
  mul_smul a b Q := ext fun x => by simp only [smul_apply, mul_smul]
  one_smul Q := ext fun x => by simp only [QuadraticForm.smul_apply, one_smul]
  smul_add a Q Q' := by
    ext
    simp only [add_apply, smul_apply, smul_add]
  smul_zero a := by
    ext
    simp only [zero_apply, smul_apply, smul_zero]

instance [Semiring S] [Module S R] [SMulCommClass S R R] : Module S (QuadraticForm R M) where
  zero_smul Q := by
    ext
    simp only [zero_apply, smul_apply, zero_smul]
  add_smul a b Q := by
    ext
    simp only [add_apply, smul_apply, add_smul]

end SemiringOperators

section RingOperators

variable [Ring R] [AddCommGroup M] [Module R M]

instance : Neg (QuadraticForm R M) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, map_smul, mul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, BilinForm.neg_apply, neg_add]⟩ }⟩

@[simp]
theorem coeFn_neg (Q : QuadraticForm R M) : ⇑(-Q) = -Q :=
  rfl
#align quadratic_form.coe_fn_neg QuadraticForm.coeFn_neg

@[simp]
theorem neg_apply (Q : QuadraticForm R M) (x : M) : (-Q) x = -Q x :=
  rfl
#align quadratic_form.neg_apply QuadraticForm.neg_apply

instance : Sub (QuadraticForm R M) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

@[simp]
theorem coeFn_sub (Q Q' : QuadraticForm R M) : ⇑(Q - Q') = Q - Q' :=
  rfl
#align quadratic_form.coe_fn_sub QuadraticForm.coeFn_sub

@[simp]
theorem sub_apply (Q Q' : QuadraticForm R M) (x : M) : (Q - Q') x = Q x - Q' x :=
  rfl
#align quadratic_form.sub_apply QuadraticForm.sub_apply

instance : AddCommGroup (QuadraticForm R M) :=
  FunLike.coe_injective.addCommGroup _ coeFn_zero coeFn_add coeFn_neg coeFn_sub
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

end RingOperators

section Comp

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {N : Type v} [AddCommMonoid N] [Module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : QuadraticForm R N) (f : M →ₗ[R] N) : QuadraticForm R M where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [map_smul, f.map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.comp f f, fun x y => by simp_rw [f.map_add, h, BilinForm.comp_apply]⟩
#align quadratic_form.comp QuadraticForm.comp

@[simp]
theorem comp_apply (Q : QuadraticForm R N) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl
#align quadratic_form.comp_apply QuadraticForm.comp_apply

/-- Compose a quadratic form with a linear function on the left. -/
@[simps (config := { simpRhs := true })]
def _root_.LinearMap.compQuadraticForm {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (f : R →ₗ[S] S) (Q : QuadraticForm R M) : QuadraticForm S M where
  toFun x := f (Q x)
  toFun_smul b x := by simp only [Q.map_smul_of_tower b x, f.map_smul, smul_eq_mul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨f.compBilinForm B, fun x y => by simp_rw [h, f.map_add, LinearMap.compBilinForm_apply]⟩
#align linear_map.comp_quadratic_form LinearMap.compQuadraticForm

end Comp

section CommRing

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The product of linear forms is a quadratic form. -/
def linMulLin (f g : M →ₗ[R] R) : QuadraticForm R M where
  toFun := f * g
  toFun_smul a x := by
    simp only [smul_eq_mul, RingHom.id_apply, Pi.mul_apply, LinearMap.map_smulₛₗ]
    ring
  exists_companion' :=
    ⟨BilinForm.linMulLin f g + BilinForm.linMulLin g f, fun x y => by
      simp
      ring⟩
#align quadratic_form.lin_mul_lin QuadraticForm.linMulLin

@[simp]
theorem linMulLin_apply (f g : M →ₗ[R] R) (x) : linMulLin f g x = f x * g x :=
  rfl
#align quadratic_form.lin_mul_lin_apply QuadraticForm.linMulLin_apply

@[simp]
theorem add_linMulLin (f g h : M →ₗ[R] R) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun _ => add_mul _ _ _
#align quadratic_form.add_lin_mul_lin QuadraticForm.add_linMulLin

@[simp]
theorem linMulLin_add (f g h : M →ₗ[R] R) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun _ => mul_add _ _ _
#align quadratic_form.lin_mul_lin_add QuadraticForm.linMulLin_add

variable {N : Type v} [AddCommMonoid N] [Module R N]

@[simp]
theorem linMulLin_comp (f g : M →ₗ[R] R) (h : N →ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl
#align quadratic_form.lin_mul_lin_comp QuadraticForm.linMulLin_comp

variable {n : Type*}

/-- `sq` is the quadratic form mapping the vector `x : R₁` to `x * x` -/
@[simps!]
def sq : QuadraticForm R R :=
  linMulLin LinearMap.id LinearMap.id
#align quadratic_form.sq QuadraticForm.sq

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : QuadraticForm R (n → R) :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => R) _ _ i) (@LinearMap.proj _ _ _ (fun _ => R) _ _ j)
#align quadratic_form.proj QuadraticForm.proj

@[simp]
theorem proj_apply (i j : n) (x : n → R) : proj i j x = x i * x j :=
  rfl
#align quadratic_form.proj_apply QuadraticForm.proj_apply

end CommRing

end QuadraticForm

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/

namespace BilinForm

open QuadraticForm

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {B : BilinForm R M}

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def toQuadraticForm (B : BilinForm R M) : QuadraticForm R M where
  toFun x := B x x
  toFun_smul a x := by simp only [mul_assoc, smul_right, smul_left]
  exists_companion' := ⟨B + BilinForm.flipHom ℕ B, fun x y => by simp [add_add_add_comm, add_comm]⟩
#align bilin_form.to_quadratic_form BilinForm.toQuadraticForm

@[simp]
theorem toQuadraticForm_apply (B : BilinForm R M) (x : M) : B.toQuadraticForm x = B x x :=
  rfl
#align bilin_form.to_quadratic_form_apply BilinForm.toQuadraticForm_apply

section

variable (R M)

@[simp]
theorem toQuadraticForm_zero : (0 : BilinForm R M).toQuadraticForm = 0 :=
  rfl
#align bilin_form.to_quadratic_form_zero BilinForm.toQuadraticForm_zero

end

@[simp]
theorem toQuadraticForm_add (B₁ B₂ : BilinForm R M) :
    (B₁ + B₂).toQuadraticForm = B₁.toQuadraticForm + B₂.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_add BilinForm.toQuadraticForm_add

@[simp]
theorem toQuadraticForm_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (a : S)
    (B : BilinForm R M) : (a • B).toQuadraticForm = a • B.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_smul BilinForm.toQuadraticForm_smul

section

variable (S R M)

/-- `BilinForm.toQuadraticForm` as an additive homomorphism -/
@[simps]
def toQuadraticFormAddMonoidHom : BilinForm R M →+ QuadraticForm R M where
  toFun := toQuadraticForm
  map_zero' := toQuadraticForm_zero _ _
  map_add' := toQuadraticForm_add
#align bilin_form.to_quadratic_form_add_monoid_hom BilinForm.toQuadraticFormAddMonoidHom

/-- `BilinForm.toQuadraticForm` as a linear map -/
@[simps!]
def toQuadraticFormLinearMap [Semiring S] [Module S R] [SMulCommClass S R R] :
    BilinForm R M →ₗ[S] QuadraticForm R M where
  toFun := toQuadraticForm
  map_smul' := toQuadraticForm_smul
  map_add' := toQuadraticForm_add

end

@[simp]
theorem toQuadraticForm_list_sum (B : List (BilinForm R M)) :
    B.sum.toQuadraticForm = (B.map toQuadraticForm).sum :=
  map_list_sum (toQuadraticFormAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_list_sum BilinForm.toQuadraticForm_list_sum

@[simp]
theorem toQuadraticForm_multiset_sum (B : Multiset (BilinForm R M)) :
    B.sum.toQuadraticForm = (B.map toQuadraticForm).sum :=
  map_multiset_sum (toQuadraticFormAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_multiset_sum BilinForm.toQuadraticForm_multiset_sum

@[simp]
theorem toQuadraticForm_sum {ι : Type*} (s : Finset ι) (B : ι → BilinForm R M) :
    (∑ i in s, B i).toQuadraticForm = ∑ i in s, (B i).toQuadraticForm :=
  map_sum (toQuadraticFormAddMonoidHom R M) B s
#align bilin_form.to_quadratic_form_sum BilinForm.toQuadraticForm_sum

@[simp]
theorem toQuadraticForm_eq_zero {B : BilinForm R M} : B.toQuadraticForm = 0 ↔ B.IsAlt :=
  QuadraticForm.ext_iff
#align bilin_form.to_quadratic_form_eq_zero BilinForm.toQuadraticForm_eq_zero

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

variable {B : BilinForm R M}

theorem polar_to_quadratic_form (x y : M) : polar (fun x => B x x) x y = B x y + B y x := by
  simp only [add_assoc, add_sub_cancel', add_right, polar, add_left_inj, add_neg_cancel_left,
    add_left, sub_eq_add_neg _ (B y y), add_comm (B y x) _]
#align bilin_form.polar_to_quadratic_form BilinForm.polar_to_quadratic_form

@[simp]
theorem toQuadraticForm_neg (B : BilinForm R M) : (-B).toQuadraticForm = -B.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_neg BilinForm.toQuadraticForm_neg

@[simp]
theorem toQuadraticForm_sub (B₁ B₂ : BilinForm R M) :
    (B₁ - B₂).toQuadraticForm = B₁.toQuadraticForm - B₂.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_sub BilinForm.toQuadraticForm_sub

end Ring

end BilinForm

namespace QuadraticForm

open BilinForm

section AssociatedHom

variable [Ring R] [CommRing R₁] [AddCommGroup M] [Module R M] [Module R₁ M]

variable (S) [CommSemiring S] [Algebra S R]

variable [Invertible (2 : R)] {B₁ : BilinForm R M}

/-- `associatedHom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `QuadraticForm.associated`, which gives an `R`-linear map.  Over a
general ring with no nontrivial distinguished commutative subring, use `QuadraticForm.associated'`,
which gives an additive homomorphism (or more precisely a `ℤ`-linear map.) -/
def associatedHom : QuadraticForm R M →ₗ[S] BilinForm R M where
  toFun Q :=
    (⟨⅟ 2, fun x => (Commute.ofNat_right x 2).invOf_right⟩ : Submonoid.center R) • Q.polarBilin
  map_add' Q Q' := by
    ext
    simp only [BilinForm.add_apply, BilinForm.smul_apply, coeFn_mk, polarBilin_apply, polar_add,
      coeFn_add, smul_add]
  map_smul' s Q := by
    ext
    -- porting note: added type annotations
    simp only [RingHom.id_apply, polar_smul, smul_comm s (_ : Submonoid.center R) (_ : R),
      polarBilin_apply, coeFn_mk, coeFn_smul, BilinForm.smul_apply]
#align quadratic_form.associated_hom QuadraticForm.associatedHom

variable (Q : QuadraticForm R M)

@[simp]
theorem associated_apply (x y : M) : associatedHom S Q x y = ⅟ 2 * (Q (x + y) - Q x - Q y) :=
  rfl
#align quadratic_form.associated_apply QuadraticForm.associated_apply

theorem associated_isSymm : (associatedHom S Q).IsSymm := fun x y => by
  simp only [associated_apply, add_comm, add_left_comm, sub_eq_add_neg, add_assoc]
#align quadratic_form.associated_is_symm QuadraticForm.associated_isSymm

@[simp]
theorem associated_comp {N : Type v} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).comp f f := by
  ext
  simp only [QuadraticForm.comp_apply, BilinForm.comp_apply, associated_apply, LinearMap.map_add]
#align quadratic_form.associated_comp QuadraticForm.associated_comp

theorem associated_toQuadraticForm (B : BilinForm R M) (x y : M) :
    associatedHom S B.toQuadraticForm x y = ⅟ 2 * (B x y + B y x) := by
  simp only [associated_apply, ← polar_to_quadratic_form, polar, toQuadraticForm_apply]
#align quadratic_form.associated_to_quadratic_form QuadraticForm.associated_toQuadraticForm

theorem associated_left_inverse (h : B₁.IsSymm) : associatedHom S B₁.toQuadraticForm = B₁ :=
  BilinForm.ext fun x y => by
    rw [associated_toQuadraticForm, h.eq x y, ← two_mul, ← mul_assoc, invOf_mul_self,
      one_mul]
#align quadratic_form.associated_left_inverse QuadraticForm.associated_left_inverse

-- porting note: moved from below to golf the next theorem
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply, map_add_self, ← three_add_one_eq_four, ← two_add_one_eq_three,
    add_mul, add_mul, one_mul, add_sub_cancel, add_sub_cancel, invOf_mul_self_assoc]
#align quadratic_form.associated_eq_self_apply QuadraticForm.associated_eq_self_apply

theorem toQuadraticForm_associated : (associatedHom S Q).toQuadraticForm = Q :=
  QuadraticForm.ext <| associated_eq_self_apply S Q
#align quadratic_form.to_quadratic_form_associated QuadraticForm.toQuadraticForm_associated

-- note: usually `rightInverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S) (BilinForm.toQuadraticForm : _ → QuadraticForm R M) :=
  fun Q => toQuadraticForm_associated S Q
#align quadratic_form.associated_right_inverse QuadraticForm.associated_rightInverse

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticForm R M →ₗ[ℤ] BilinForm R M :=
  associatedHom ℤ
#align quadratic_form.associated' QuadraticForm.associated'

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance canLift : CanLift (BilinForm R M) (QuadraticForm R M) (associatedHom ℕ) BilinForm.IsSymm
    where prf B hB := ⟨B.toQuadraticForm, associated_left_inverse _ hB⟩
#align quadratic_form.can_lift QuadraticForm.canLift

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
theorem exists_quadraticForm_ne_zero {Q : QuadraticForm R M}
    -- Porting note: added implicit argument
    (hB₁ : associated' (R := R) Q ≠ 0) :
    ∃ x, Q x ≠ 0 := by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticForm.ext h : Q = 0), LinearMap.map_zero]
#align quadratic_form.exists_quadratic_form_ne_zero QuadraticForm.exists_quadraticForm_ne_zero

end AssociatedHom

section Associated

variable [CommRing R₁] [AddCommGroup M] [Module R₁ M]

variable [Invertible (2 : R₁)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associatedHom` and place it in the previous section.
/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
abbrev associated : QuadraticForm R₁ M →ₗ[R₁] BilinForm R₁ M :=
  associatedHom R₁
#align quadratic_form.associated QuadraticForm.associated

@[simp]
theorem associated_linMulLin (f g : M →ₗ[R₁] R₁) :
    associated (R₁ := R₁) (linMulLin f g) =
      ⅟ (2 : R₁) • (BilinForm.linMulLin f g + BilinForm.linMulLin g f) := by
  ext
  simp only [smul_add, Algebra.id.smul_eq_mul, BilinForm.linMulLin_apply,
    QuadraticForm.linMulLin_apply, BilinForm.smul_apply, associated_apply, BilinForm.add_apply,
    LinearMap.map_add]
  ring
#align quadratic_form.associated_lin_mul_lin QuadraticForm.associated_linMulLin

@[simp]
lemma associated_sq : associated (R₁ := R₁) sq = LinearMap.toBilin (LinearMap.mul R₁ R₁) :=
  (associated_linMulLin (LinearMap.id) (LinearMap.id)).trans <|
    by simp only [smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

end Associated

section Anisotropic

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def Anisotropic (Q : QuadraticForm R M) : Prop :=
  ∀ x, Q x = 0 → x = 0
#align quadratic_form.anisotropic QuadraticForm.Anisotropic

theorem not_anisotropic_iff_exists (Q : QuadraticForm R M) :
    ¬Anisotropic Q ↔ ∃ x, x ≠ 0 ∧ Q x = 0 := by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]
#align quadratic_form.not_anisotropic_iff_exists QuadraticForm.not_anisotropic_iff_exists

theorem Anisotropic.eq_zero_iff {Q : QuadraticForm R M} (h : Anisotropic Q) {x : M} :
    Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero Q⟩
#align quadratic_form.anisotropic.eq_zero_iff QuadraticForm.Anisotropic.eq_zero_iff

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem nondegenerate_of_anisotropic [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hB : Q.Anisotropic) :
    -- Porting note: added implicit argument
    (QuadraticForm.associated' (R := R) Q).Nondegenerate := fun x hx ↦ hB _ <| by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm
#align quadratic_form.nondegenerate_of_anisotropic QuadraticForm.nondegenerate_of_anisotropic

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [OrderedRing R₂] [AddCommMonoid M] [Module R₂ M]

variable {Q₂ : QuadraticForm R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def PosDef (Q₂ : QuadraticForm R₂ M) : Prop :=
  ∀ x, x ≠ 0 → 0 < Q₂ x
#align quadratic_form.pos_def QuadraticForm.PosDef

theorem PosDef.smul {R} [LinearOrderedCommRing R] [Module R M] {Q : QuadraticForm R M}
    (h : PosDef Q) {a : R} (a_pos : 0 < a) : PosDef (a • Q) := fun x hx => mul_pos a_pos (h x hx)
#align quadratic_form.pos_def.smul QuadraticForm.PosDef.smul

variable {n : Type*}

theorem PosDef.nonneg {Q : QuadraticForm R₂ M} (hQ : PosDef Q) (x : M) : 0 ≤ Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le
#align quadratic_form.pos_def.nonneg QuadraticForm.PosDef.nonneg

theorem PosDef.anisotropic {Q : QuadraticForm R₂ M} (hQ : Q.PosDef) : Q.Anisotropic := fun x hQx =>
  by_contradiction fun hx =>
    lt_irrefl (0 : R₂) <| by
      have := hQ _ hx
      rw [hQx] at this
      exact this
#align quadratic_form.pos_def.anisotropic QuadraticForm.PosDef.anisotropic

theorem posDef_of_nonneg {Q : QuadraticForm R₂ M} (h : ∀ x, 0 ≤ Q x) (h0 : Q.Anisotropic) :
    PosDef Q := fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)
#align quadratic_form.pos_def_of_nonneg QuadraticForm.posDef_of_nonneg

theorem posDef_iff_nonneg {Q : QuadraticForm R₂ M} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩
#align quadratic_form.pos_def_iff_nonneg QuadraticForm.posDef_iff_nonneg

theorem PosDef.add (Q Q' : QuadraticForm R₂ M) (hQ : PosDef Q) (hQ' : PosDef Q') :
    PosDef (Q + Q') := fun x hx => add_pos (hQ x hx) (hQ' x hx)
#align quadratic_form.pos_def.add QuadraticForm.PosDef.add

theorem linMulLinSelfPosDef {R} [LinearOrderedCommRing R] [Module R M] (f : M →ₗ[R] R)
    (hf : LinearMap.ker f = ⊥) : PosDef (linMulLin f f) := fun _x hx =>
  mul_self_pos.2 fun h => hx <| LinearMap.ker_eq_bot'.mp hf _ h
#align quadratic_form.lin_mul_lin_self_pos_def QuadraticForm.linMulLinSelfPosDef

end PosDef

end QuadraticForm

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variable {n : Type w} [Fintype n] [DecidableEq n]

variable [CommRing R₁] [AddCommMonoid M] [Module R₁ M]

/-- `M.toQuadraticForm'` is the map `fun x ↦ col x * M * row x` as a quadratic form. -/
def Matrix.toQuadraticForm' (M : Matrix n n R₁) : QuadraticForm R₁ (n → R₁) :=
  M.toBilin'.toQuadraticForm
#align matrix.to_quadratic_form' Matrix.toQuadraticForm'

variable [Invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def QuadraticForm.toMatrix' (Q : QuadraticForm R₁ (n → R₁)) : Matrix n n R₁ :=
  BilinForm.toMatrix' (associated (R₁ := R₁) Q)
#align quadratic_form.to_matrix' QuadraticForm.toMatrix'

open QuadraticForm

theorem QuadraticForm.toMatrix'_smul (a : R₁) (Q : QuadraticForm R₁ (n → R₁)) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp only [toMatrix', LinearEquiv.map_smul, LinearMap.map_smul]
#align quadratic_form.to_matrix'_smul QuadraticForm.toMatrix'_smul

theorem QuadraticForm.isSymm_toMatrix' (Q : QuadraticForm R₁ (n → R₁)) : Q.toMatrix'.IsSymm := by
  ext i j
  rw [toMatrix', Matrix.transpose_apply, BilinForm.toMatrix'_apply, BilinForm.toMatrix'_apply,
    associated_isSymm]
#align quadratic_form.is_symm_to_matrix' QuadraticForm.isSymm_toMatrix'

end

namespace QuadraticForm

variable {n : Type w} [Fintype n]

variable [CommRing R₁] [DecidableEq n] [Invertible (2 : R₁)]

variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
theorem toMatrix'_comp (Q : QuadraticForm R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] m → R₁) :
    (Q.comp f).toMatrix' = (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f) := by
  ext
  simp only [QuadraticForm.associated_comp, BilinForm.toMatrix'_comp, toMatrix']
#align quadratic_form.to_matrix'_comp QuadraticForm.toMatrix'_comp

section Discriminant

variable {Q : QuadraticForm R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticForm R₁ (n → R₁)) : R₁ :=
  Q.toMatrix'.det
#align quadratic_form.discr QuadraticForm.discr

theorem discr_smul (a : R₁) : (a • Q).discr = a ^ Fintype.card n * Q.discr := by
  simp only [discr, toMatrix'_smul, Matrix.det_smul]
#align quadratic_form.discr_smul QuadraticForm.discr_smul

theorem discr_comp (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (Q.comp f).discr = f.toMatrix'.det * f.toMatrix'.det * Q.discr := by
  simp only [Matrix.det_transpose, mul_left_comm, QuadraticForm.toMatrix'_comp, mul_comm,
    Matrix.det_mul, discr]
#align quadratic_form.discr_comp QuadraticForm.discr_comp

end Discriminant

end QuadraticForm

namespace QuadraticForm

end QuadraticForm

namespace BilinForm

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
theorem nondegenerate_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticForm.Anisotropic) :
    B.Nondegenerate := fun x hx => hB _ (hx x)
#align bilin_form.nondegenerate_of_anisotropic BilinForm.nondegenerate_of_anisotropic

end Semiring

variable [Ring R] [AddCommGroup M] [Module R M]

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M} (hB₁ : B ≠ 0)
    (hB₂ : B.IsSymm) : ∃ x, ¬B.IsOrtho x x := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticForm.exists_quadraticForm_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩
#align bilin_form.exists_bilin_form_self_ne_zero BilinForm.exists_bilinForm_self_ne_zero

open FiniteDimensional

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : BilinForm K V} (hB₂ : B.IsSymm) :
    ∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v := by
  induction' hd : finrank K V with d ih generalizing V
  · simp_rw [Nat.zero_eq]
    exact ⟨basisOfFinrankZero hd, fun _ _ _ => zero_left _⟩
  haveI := finrank_pos_iff.1 (hd.symm ▸ Nat.succ_pos d : 0 < finrank K V)
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := FiniteDimensional.finBasis K V
    rw [hd] at b
    refine' ⟨b, fun i j _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilinForm_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_not_isOrtho_self x hx)] at hd
  let B' := B.restrict (B.orthogonal <| K ∙ x)
  obtain ⟨v', hv₁⟩ := ih (B.restrictSymm hB₂ _ : B'.IsSymm) (Nat.succ.inj hd)
  -- concatenate `x` with the basis obtained by induction
  let b :=
    Basis.mkFinCons x v'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have := (isCompl_span_singleton_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ zero_left _)
      (by
        intro y
        refine' ⟨-B x y / B x x, fun z hz => _⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [IsOrtho, smul_left, add_right, smul_right, div_mul_cancel _ hx, add_neg_self,
          mul_zero])
  refine' ⟨b, _⟩
  · rw [Basis.coe_mkFinCons]
    intro j i
    refine' Fin.cases _ (fun i => _) i <;> refine' Fin.cases _ (fun j => _) j <;> intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    · exact (hij rfl).elim
    · rw [IsOrtho, hB₂]
      exact (v' j).prop _ (Submodule.mem_span_singleton_self x)
    · exact (v' i).prop _ (Submodule.mem_span_singleton_self x)
    · exact hv₁ (ne_of_apply_ne _ hij)
#align bilin_form.exists_orthogonal_basis BilinForm.exists_orthogonal_basis

end BilinForm

namespace QuadraticForm

open Finset BilinForm

variable {M₁ : Type*} [Semiring R] [CommSemiring R₁] [AddCommMonoid M] [AddCommMonoid M₁]

variable [Module R M] [Module R M₁]

variable {ι : Type*} [Fintype ι] {v : Basis ι R M}

/-- Given a quadratic form `Q` and a basis, `basisRepr` is the basis representation of `Q`. -/
noncomputable def basisRepr (Q : QuadraticForm R M) (v : Basis ι R M) : QuadraticForm R (ι → R) :=
  Q.comp v.equivFun.symm
#align quadratic_form.basis_repr QuadraticForm.basisRepr

@[simp]
theorem basisRepr_apply (Q : QuadraticForm R M) (w : ι → R) :
    Q.basisRepr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equivFun_symm_apply]
  rfl
#align quadratic_form.basis_repr_apply QuadraticForm.basisRepr_apply

section

variable (R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[Algebra S R₁]`, although this is stated more generally. -/
def weightedSumSquares [Monoid S] [DistribMulAction S R₁] [SMulCommClass S R₁ R₁] (w : ι → S) :
    QuadraticForm R₁ (ι → R₁) :=
  ∑ i : ι, w i • proj i i
#align quadratic_form.weighted_sum_squares QuadraticForm.weightedSumSquares

end

@[simp]
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R₁] [SMulCommClass S R₁ R₁]
    (w : ι → S) (v : ι → R₁) : weightedSumSquares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticForm.sum_apply _ _ _
#align quadratic_form.weighted_sum_squares_apply QuadraticForm.weightedSumSquares_apply

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basisRepr_eq_of_iIsOrtho {R₁ M} [CommRing R₁] [AddCommGroup M] [Module R₁ M]
    [Invertible (2 : R₁)] (Q : QuadraticForm R₁ M) (v : Basis ι R₁ M)
    (hv₂ : (associated (R₁ := R₁) Q).iIsOrtho v) :
    Q.basisRepr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basisRepr_apply, ← @associated_eq_self_apply R₁, sum_left, weightedSumSquares_apply]
  refine' sum_congr rfl fun j hj => _
  rw [← @associated_eq_self_apply R₁, sum_right, sum_eq_single_of_mem j hj]
  · rw [smul_left, smul_right, smul_eq_mul]
    ring
  · intro i _ hij
    rw [smul_left, smul_right, show associatedHom R₁ Q (v j) (v i) = 0 from hv₂ hij.symm,
      mul_zero, mul_zero]
set_option linter.uppercaseLean3 false in
#align quadratic_form.basis_repr_eq_of_is_Ortho QuadraticForm.basisRepr_eq_of_iIsOrtho

end QuadraticForm
