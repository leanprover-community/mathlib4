/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric

#align_import linear_algebra.quadratic_form.basic from "leanprover-community/mathlib"@"d11f435d4e34a6cea0a1797d6b625b0c170be845"

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form on a commutative ring `R` is a map `Q : M → R` such that:

* `QuadraticForm.map_smul`: `Q (a • x) = a * a * Q x`
* `QuadraticForm.polar_add_left`, `QuadraticForm.polar_add_right`,
  `QuadraticForm.polar_smul_left`, `QuadraticForm.polar_smul_right`:
  the map `QuadraticForm.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to commutative semirings using the approach in [izhakian2016][] which
requires that there be a (possibly non-unique) companion bilinear form `B` such that
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
 * `QuadraticForm.IsOrtho`: orthogonality of vectors with respect to a quadratic form.

## Main statements

 * `QuadraticForm.associated_left_inverse`,
 * `QuadraticForm.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms
 * `LinearMap.BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear form `B`.

## Notation

In this file, the variable `R` is used when a `CommSemiring` structure is available.

The variable `S` is used when `R` itself has a `•` action.

## Implementation notes

While the definition and many results make sense if we drop commutativity assumptions,
the correct definition of a quadratic form in the noncommutative setting would require
substantial refactors from the current version, such that $Q(rm) = rQ(m)r^*$ for some
suitable conjugation $r^*$.

The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Maps/near/395529867)
has some further discusion.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/


universe u v w

variable {S T : Type*}
variable {R : Type*} {M N : Type*}

open LinearMap (BilinForm)

section Polar

variable [CommRing R] [AddCommGroup M]

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

theorem polar_comp {F : Type*} [CommRing S] [FunLike F R S] [AddMonoidHomClass F R S]
    (f : M → R) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Pi.smul_apply, Function.comp_apply, map_sub]
#align quadratic_form.polar_comp QuadraticForm.polar_comp

end QuadraticForm

end Polar

/-- A quadratic form over a module.

For a more familiar constructor when `R` is a ring, see `QuadraticForm.ofPolar`. -/
structure QuadraticForm (R : Type u) (M : Type v)
    [CommSemiring R] [AddCommMonoid M] [Module R M] where
  toFun : M → R
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = a * a * toFun x
  exists_companion' :
    ∃ B : BilinForm R M, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y
#align quadratic_form QuadraticForm

namespace QuadraticForm

section DFunLike

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {Q Q' : QuadraticForm R M}

instance instFunLike : FunLike (QuadraticForm R M) M R where
  coe := toFun
  coe_injective' x y h := by cases x; cases y; congr
#align quadratic_form.fun_like QuadraticForm.instFunLike

/-- Helper instance for when there's too many metavariables to apply
`DFunLike.hasCoeToFun` directly. -/
instance : CoeFun (QuadraticForm R M) fun _ => M → R :=
  ⟨DFunLike.coe⟩

variable (Q)

/-- The `simp` normal form for a quadratic form is `DFunLike.coe`, not `toFun`. -/
@[simp]
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl
#align quadratic_form.to_fun_eq_coe QuadraticForm.toFun_eq_coe

-- this must come after the coe_to_fun definition
initialize_simps_projections QuadraticForm (toFun → apply)

variable {Q}

@[ext]
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  DFunLike.ext _ _ H
#align quadratic_form.ext QuadraticForm.ext

theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  DFunLike.congr_fun h _
#align quadratic_form.congr_fun QuadraticForm.congr_fun

theorem ext_iff : Q = Q' ↔ ∀ x, Q x = Q' x :=
  DFunLike.ext_iff
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
  DFunLike.ext' h
#align quadratic_form.copy_eq QuadraticForm.copy_eq

end DFunLike

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
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
  simp only [h, map_add, LinearMap.add_apply]
  abel
#align quadratic_form.map_add_add_add_map QuadraticForm.map_add_add_add_map

theorem map_add_self (x : M) : Q (x + x) = 4 * Q x := by
  rw [← one_smul R x, ← add_smul, map_smul]
  norm_num
#align quadratic_form.map_add_self QuadraticForm.map_add_self

-- Porting note: removed @[simp] because it is superseded by `ZeroHomClass.map_zero`
theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]
#align quadratic_form.map_zero QuadraticForm.map_zero

instance zeroHomClass : ZeroHomClass (QuadraticForm R M) M R where
  map_zero := map_zero
#align quadratic_form.zero_hom_class QuadraticForm.zeroHomClass

theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x, map_smul, ← RingHom.map_mul, Algebra.smul_def]
#align quadratic_form.map_smul_of_tower QuadraticForm.map_smul_of_tower

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M]
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
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left, smul_eq_mul]
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

/-- `QuadraticForm.polar` as a bilinear map -/
@[simps!]
def polarBilin : BilinForm R M :=
  LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)
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
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ ↦ by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ ↦ by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ ↦ by
        simp only [LinearMap.mk₂_apply]
        rw [polar, sub_sub, add_sub_cancel]⟩ }
#align quadratic_form.of_polar QuadraticForm.ofPolar

/-- In a ring the companion bilinear form is unique and equal to `QuadraticForm.polar`. -/
theorem choose_exists_companion : Q.exists_companion.choose = polarBilin Q :=
  LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply, polar, Q.exists_companion.choose_spec, sub_sub,
      add_sub_cancel_left]
#align quadratic_form.some_exists_companion QuadraticForm.choose_exists_companion

end CommRing

section SemiringOperators

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section SMul

variable [Monoid S] [Monoid T] [DistribMulAction S R] [DistribMulAction T R]
variable [SMulCommClass S R R] [SMulCommClass T R R]

/-- `QuadraticForm R M` inherits the scalar action from any algebra over `R`.

This provides an `R`-action via `Algebra.id`. -/
instance : SMul S (QuadraticForm R M) :=
  ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by rw [Pi.smul_apply, map_smul, Pi.smul_apply, mul_smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R R
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
  smul_comm _s _t _q := ext fun _ => smul_comm _ _ _

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticForm R M) where
  smul_assoc _s _t _q := ext fun _ => smul_assoc _ _ _

end SMul

instance : Zero (QuadraticForm R M) :=
  ⟨{  toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [mul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩

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
          simp_rw [Pi.add_apply, h, h', LinearMap.add_apply, add_add_add_comm]⟩ }⟩

@[simp]
theorem coeFn_add (Q Q' : QuadraticForm R M) : ⇑(Q + Q') = Q + Q' :=
  rfl
#align quadratic_form.coe_fn_add QuadraticForm.coeFn_add

@[simp]
theorem add_apply (Q Q' : QuadraticForm R M) (x : M) : (Q + Q') x = Q x + Q' x :=
  rfl
#align quadratic_form.add_apply QuadraticForm.add_apply

instance : AddCommMonoid (QuadraticForm R M) :=
  DFunLike.coe_injective.addCommMonoid _ coeFn_zero coeFn_add fun _ _ => coeFn_smul _ _

/-- `@CoeFn (QuadraticForm R M)` as an `AddMonoidHom`.

This API mirrors `AddMonoidHom.coeFn`. -/
@[simps apply]
def coeFnAddMonoidHom : QuadraticForm R M →+ M → R where
  toFun := DFunLike.coe
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
    ⇑(∑ i ∈ s, Q i) = ∑ i ∈ s, ⇑(Q i) :=
  map_sum coeFnAddMonoidHom Q s
#align quadratic_form.coe_fn_sum QuadraticForm.coeFn_sum

@[simp]
theorem sum_apply {ι : Type*} (Q : ι → QuadraticForm R M) (s : Finset ι) (x : M) :
    (∑ i ∈ s, Q i) x = ∑ i ∈ s, Q i x :=
  map_sum (evalAddMonoidHom x : _ →+ R) Q s
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

instance [Semiring S] [Module S R] [SMulCommClass S R R] :
    Module S (QuadraticForm R M) where
  zero_smul Q := by
    ext
    simp only [zero_apply, smul_apply, zero_smul]
  add_smul a b Q := by
    ext
    simp only [add_apply, smul_apply, add_smul]

end SemiringOperators

section RingOperators

variable [CommRing R] [AddCommGroup M] [Module R M]

instance : Neg (QuadraticForm R M) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, map_smul, mul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩

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
  DFunLike.coe_injective.addCommGroup _ coeFn_zero coeFn_add coeFn_neg coeFn_sub
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

end RingOperators

section Comp

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : QuadraticForm R N) (f : M →ₗ[R] N) : QuadraticForm R M where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [map_smul, f.map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩
#align quadratic_form.comp QuadraticForm.comp

@[simp]
theorem comp_apply (Q : QuadraticForm R N) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl
#align quadratic_form.comp_apply QuadraticForm.comp_apply

/-- Compose a quadratic form with a linear function on the left. -/
@[simps (config := { simpRhs := true })]
def _root_.LinearMap.compQuadraticForm [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (f : R →ₗ[S] S) (Q : QuadraticForm R M) : QuadraticForm S M where
  toFun x := f (Q x)
  toFun_smul b x := by simp only [Q.map_smul_of_tower b x, f.map_smul, smul_eq_mul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨(B.restrictScalars₁₂ S S).compr₂ f, fun x y => by
      simp_rw [h, f.map_add, LinearMap.compr₂_apply, LinearMap.restrictScalars₁₂_apply_apply]⟩
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
    ⟨(LinearMap.mul R R).compl₁₂ f g + (LinearMap.mul R R).compl₁₂ g f, fun x y => by
      simp only [Pi.mul_apply, map_add, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
        LinearMap.add_apply]
      ring_nf⟩
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

variable [AddCommMonoid N] [Module R N]

@[simp]
theorem linMulLin_comp (f g : M →ₗ[R] R) (h : N →ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl
#align quadratic_form.lin_mul_lin_comp QuadraticForm.linMulLin_comp

variable {n : Type*}

/-- `sq` is the quadratic form mapping the vector `x : R` to `x * x` -/
@[simps!]
def sq : QuadraticForm R R :=
  linMulLin LinearMap.id LinearMap.id
#align quadratic_form.sq QuadraticForm.sq

/-- `proj i j` is the quadratic form mapping the vector `x : n → R` to `x i * x j` -/
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

namespace LinearMap

namespace BilinForm

open QuadraticForm

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- A bilinear map into `R` gives a quadratic form by applying the argument twice. -/
def toQuadraticForm (B : BilinForm R M) : QuadraticForm R M where
  toFun x := B x x
  toFun_smul a x := by
    simp only [_root_.map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc]
  exists_companion' := ⟨B + B.flip,
    fun x y => by simp only [map_add, LinearMap.add_apply, LinearMap.flip_apply]; abel⟩
#align bilin_form.to_quadratic_form LinearMap.BilinForm.toQuadraticForm

variable {B : BilinForm R M}

@[simp]
theorem toQuadraticForm_apply (B : BilinForm R M) (x : M) : B.toQuadraticForm x = B x x :=
  rfl
#align bilin_form.to_quadratic_form_apply LinearMap.BilinForm.toQuadraticForm_apply

theorem toQuadraticForm_comp_same (B : BilinForm R N) (f : M →ₗ[R] N) :
    BilinForm.toQuadraticForm (B.compl₁₂ f f) = B.toQuadraticForm.comp f := rfl

section

variable (R M)

@[simp]
theorem toQuadraticForm_zero : (0 : BilinForm R M).toQuadraticForm = 0 :=
  rfl
#align bilin_form.to_quadratic_form_zero LinearMap.BilinForm.toQuadraticForm_zero

end

@[simp]
theorem toQuadraticForm_add (B₁ B₂ : BilinForm R M) :
    (B₁ + B₂).toQuadraticForm = B₁.toQuadraticForm + B₂.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_add LinearMap.BilinForm.toQuadraticForm_add

@[simp]
theorem toQuadraticForm_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (a : S) (B : BilinForm R M) :
    letI := SMulCommClass.symm S R R
    (a • B).toQuadraticForm = a • B.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_smul LinearMap.BilinForm.toQuadraticForm_smul

section

variable (S R M)

/-- `LinearMap.BilinForm.toQuadraticForm` as an additive homomorphism -/
@[simps]
def toQuadraticFormAddMonoidHom : BilinForm R M →+ QuadraticForm R M where
  toFun := toQuadraticForm
  map_zero' := toQuadraticForm_zero _ _
  map_add' := toQuadraticForm_add
#align bilin_form.to_quadratic_form_add_monoid_hom LinearMap.BilinForm.toQuadraticFormAddMonoidHom

/-- `LinearMap.BilinForm.toQuadraticForm` as a linear map -/
@[simps!]
def toQuadraticFormLinearMap [Semiring S] [Module S R] [SMulCommClass S R R] [SMulCommClass R S R] :
    BilinForm R M →ₗ[S] QuadraticForm R M where
  toFun := toQuadraticForm
  map_smul' := toQuadraticForm_smul
  map_add' := toQuadraticForm_add

end

@[simp]
theorem toQuadraticForm_list_sum (B : List (BilinForm R M)) :
    B.sum.toQuadraticForm = (B.map toQuadraticForm).sum :=
  map_list_sum (toQuadraticFormAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_list_sum LinearMap.BilinForm.toQuadraticForm_list_sum

@[simp]
theorem toQuadraticForm_multiset_sum (B : Multiset (BilinForm R M)) :
    B.sum.toQuadraticForm = (B.map toQuadraticForm).sum :=
  map_multiset_sum (toQuadraticFormAddMonoidHom R M) B
#align bilin_form.to_quadratic_form_multiset_sum LinearMap.BilinForm.toQuadraticForm_multiset_sum

@[simp]
theorem toQuadraticForm_sum {ι : Type*} (s : Finset ι) (B : ι → BilinForm R M) :
    (∑ i ∈ s, B i).toQuadraticForm = ∑ i ∈ s, (B i).toQuadraticForm :=
  map_sum (toQuadraticFormAddMonoidHom R M) B s
#align bilin_form.to_quadratic_form_sum LinearMap.BilinForm.toQuadraticForm_sum

@[simp]
theorem toQuadraticForm_eq_zero {B : BilinForm R M} : B.toQuadraticForm = 0 ↔ B.IsAlt :=
  QuadraticForm.ext_iff
#align bilin_form.to_quadratic_form_eq_zero LinearMap.BilinForm.toQuadraticForm_eq_zero

end Semiring

section Ring

open QuadraticForm

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {B : BilinForm R M}

@[simp]
theorem toQuadraticForm_neg (B : BilinForm R M) : (-B).toQuadraticForm = -B.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_neg LinearMap.BilinForm.toQuadraticForm_neg

@[simp]
theorem toQuadraticForm_sub (B₁ B₂ : BilinForm R M) :
    (B₁ - B₂).toQuadraticForm = B₁.toQuadraticForm - B₂.toQuadraticForm :=
  rfl
#align bilin_form.to_quadratic_form_sub LinearMap.BilinForm.toQuadraticForm_sub

theorem polar_toQuadraticForm (x y : M) : polar (toQuadraticForm B) x y = B x y + B y x := by
  simp only [toQuadraticForm_apply, add_assoc, add_sub_cancel_left, add_apply, polar, add_left_inj,
    add_neg_cancel_left, map_add, sub_eq_add_neg _ (B y y), add_comm (B y x) _]
#align bilin_form.polar_to_quadratic_form LinearMap.BilinForm.polar_toQuadraticForm

theorem polarBilin_toQuadraticForm : polarBilin (toQuadraticForm B) = B + B.flip :=
  ext₂ polar_toQuadraticForm

@[simp] theorem _root_.QuadraticForm.toQuadraticForm_polarBilin (Q : QuadraticForm R M) :
    toQuadraticForm (polarBilin Q) = 2 • Q :=
  QuadraticForm.ext fun x => (polar_self _ x).trans <| by simp

theorem  _root_.QuadraticForm.polarBilin_injective (h : IsUnit (2 : R)) :
    Function.Injective (polarBilin : QuadraticForm R M → _) :=
  fun Q₁ Q₂ h₁₂ => QuadraticForm.ext fun x => h.mul_left_cancel <| by
    simpa using DFunLike.congr_fun (congr_arg toQuadraticForm h₁₂) x

variable [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M]
variable [AddCommGroup N] [Module R N]

theorem _root_.QuadraticForm.polarBilin_comp (Q : QuadraticForm R N) (f : M →ₗ[R] N) :
    polarBilin (Q.comp f) = compl₁₂ (polarBilin Q) f f :=
  ext₂ fun x y => by simp [polar]

theorem compQuadraticForm_polar (f : R →ₗ[S] S) (Q : QuadraticForm R M) (x y : M) :
    polar (f.compQuadraticForm Q) x y = f (polar Q x y) := by
  simp [polar]

theorem compQuadraticForm_polarBilin (f : R →ₗ[S] S) (Q : QuadraticForm R M) :
    (f.compQuadraticForm Q).polarBilin =
    (Q.polarBilin.restrictScalars₁₂ S S).compr₂ f :=
  ext₂ <| compQuadraticForm_polar _ _

end Ring

end BilinForm

end LinearMap

namespace QuadraticForm

open LinearMap.BilinForm

section AssociatedHom

variable [CommRing R] [AddCommGroup M] [Module R M]
variable (S) [CommSemiring S] [Algebra S R]
variable [Invertible (2 : R)] {B₁ : BilinForm R M}

/-- `associatedHom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `QuadraticForm.associated`, which gives an `R`-linear map.  Over a
general ring with no nontrivial distinguished commutative subring, use `QuadraticForm.associated'`,
which gives an additive homomorphism (or more precisely a `ℤ`-linear map.) -/
def associatedHom : QuadraticForm R M →ₗ[S] BilinForm R M :=
  -- TODO: this `center` stuff is vertigial from an incorrect non-commutative version, but we leave
  -- it behind to make a future refactor to a *correct* non-commutative version easier in future.
  (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    { toFun := polarBilin
      map_add' := fun _x _y => LinearMap.ext₂ <| polar_add _ _
      map_smul' := fun _c _x => LinearMap.ext₂ <| polar_smul _ _ }
#align quadratic_form.associated_hom QuadraticForm.associatedHom

variable (Q : QuadraticForm R M)

@[simp]
theorem associated_apply (x y : M) : associatedHom S Q x y = ⅟ 2 * (Q (x + y) - Q x - Q y) :=
  rfl
#align quadratic_form.associated_apply QuadraticForm.associated_apply

@[simp] theorem two_nsmul_associated : 2 • associatedHom S Q = Q.polarBilin := by
  ext
  dsimp
  rw [← smul_mul_assoc, two_nsmul, invOf_two_add_invOf_two, one_mul, polar]

theorem associated_isSymm : (associatedHom S Q).IsSymm := fun x y => by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, map_mul, RingHom.id_apply, map_add,
    _root_.map_neg, add_comm, add_left_comm]
#align quadratic_form.associated_is_symm QuadraticForm.associated_isSymm

@[simp]
theorem associated_comp [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).compl₁₂ f f := by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]
#align quadratic_form.associated_comp QuadraticForm.associated_comp

theorem associated_toQuadraticForm (B : BilinForm R M) (x y : M) :
    associatedHom S B.toQuadraticForm x y = ⅟ 2 * (B x y + B y x) := by
  simp only [associated_apply, toQuadraticForm_apply, map_add, add_apply, ← polar_toQuadraticForm,
    polar.eq_1]
#align quadratic_form.associated_to_quadratic_form QuadraticForm.associated_toQuadraticForm

theorem associated_left_inverse (h : B₁.IsSymm) : associatedHom S B₁.toQuadraticForm = B₁ :=
  LinearMap.ext₂ fun x y => by
    rw [associated_toQuadraticForm, ← h.eq, RingHom.id_apply, ← two_mul, ← mul_assoc,
      invOf_mul_self, one_mul]
#align quadratic_form.associated_left_inverse QuadraticForm.associated_left_inverse

-- Porting note: moved from below to golf the next theorem
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply, map_add_self, ← three_add_one_eq_four, ← two_add_one_eq_three,
    add_mul, add_mul, one_mul, add_sub_cancel_right, add_sub_cancel_right, invOf_mul_self_assoc]
#align quadratic_form.associated_eq_self_apply QuadraticForm.associated_eq_self_apply

theorem toQuadraticForm_associated : (associatedHom S Q).toQuadraticForm = Q :=
  QuadraticForm.ext <| associated_eq_self_apply S Q
#align quadratic_form.to_quadratic_form_associated QuadraticForm.toQuadraticForm_associated

-- note: usually `rightInverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S) (toQuadraticForm : _ → QuadraticForm R M) :=
  fun Q => toQuadraticForm_associated S Q
#align quadratic_form.associated_right_inverse QuadraticForm.associated_rightInverse

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticForm R M →ₗ[ℤ] BilinForm R M :=
  associatedHom ℤ
#align quadratic_form.associated' QuadraticForm.associated'

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance canLift :
    CanLift (BilinForm R M) (QuadraticForm R M) (associatedHom ℕ) LinearMap.IsSymm where
  prf B hB := ⟨B.toQuadraticForm, associated_left_inverse _ hB⟩
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

variable [CommSemiring S] [CommRing R] [AddCommGroup M] [Algebra S R] [Module R M]
variable [Invertible (2 : R)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associatedHom` and place it in the previous section.
/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
abbrev associated : QuadraticForm R M →ₗ[R] BilinForm R M :=
  associatedHom R
#align quadratic_form.associated QuadraticForm.associated

variable (S) in
theorem coe_associatedHom :
    ⇑(associatedHom S : QuadraticForm R M →ₗ[S] BilinForm R M) = associated :=
  rfl

open LinearMap in
@[simp]
theorem associated_linMulLin (f g : M →ₗ[R] R) :
    associated (R := R) (linMulLin f g) =
      ⅟ (2 : R) • ((mul R R).compl₁₂ f g + (mul R R).compl₁₂ g f) := by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul]
  ring_nf
#align quadratic_form.associated_lin_mul_lin QuadraticForm.associated_linMulLin

open LinearMap in
@[simp]
lemma associated_sq : associated (R := R) sq = mul R R :=
  (associated_linMulLin (id) (id)).trans <|
    by simp only [smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

end Associated

section IsOrtho

/-! ### Orthogonality -/

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M] {Q : QuadraticForm R M}

/-- The proposition that two elements of a quadratic form space are orthogonal. -/
def IsOrtho (Q : QuadraticForm R M) (x y : M) : Prop :=
  Q (x + y) = Q x + Q y

theorem isOrtho_def {Q : QuadraticForm R M} {x y : M} : Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y :=
  Iff.rfl

theorem IsOrtho.all (x y : M) : IsOrtho (0 : QuadraticForm R M) x y := (zero_add _).symm

theorem IsOrtho.zero_left (x : M) : IsOrtho Q (0 : M) x := by simp [isOrtho_def]

theorem IsOrtho.zero_right (x : M) : IsOrtho Q x (0 : M) := by simp [isOrtho_def]

theorem ne_zero_of_not_isOrtho_self {Q : QuadraticForm R M} (x : M) (hx₁ : ¬Q.IsOrtho x x) :
    x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)

theorem isOrtho_comm {x y : M} : IsOrtho Q x y ↔ IsOrtho Q y x := by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm

theorem _root_.LinearMap.BilinForm.toQuadraticForm_isOrtho [IsCancelAdd R]
    [NoZeroDivisors R] [CharZero R] {B : BilinForm R M} {x y : M} (h : B.IsSymm):
    B.toQuadraticForm.IsOrtho x y ↔ B.IsOrtho x y := by
  letI : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstanceAs <| AddCommMonoid R) with }
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, toQuadraticForm_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_right_eq_self (a := B x x + B y y), ← h, RingHom.id_apply, add_self_eq_zero]

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

@[simp]
theorem isOrtho_polarBilin {x y : M} : Q.polarBilin.IsOrtho x y ↔ IsOrtho Q x y := by
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, polarBilin_apply_apply, polar, sub_sub,
    sub_eq_zero]

theorem IsOrtho.polar_eq_zero {x y : M} (h : IsOrtho Q x y) : polar Q x y = 0 :=
  isOrtho_polarBilin.mpr h

@[simp]
theorem associated_isOrtho [Invertible (2 : R)] {x y : M} :
    Q.associated.IsOrtho x y ↔ Q.IsOrtho x y := by
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, associated_apply, invOf_mul_eq_iff_eq_mul_left,
    mul_zero, sub_sub, sub_eq_zero]

end CommRing

end IsOrtho

section Anisotropic

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

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

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticForm R M)
    (hB : Q.Anisotropic) :
    -- Porting note: added implicit argument
    (QuadraticForm.associated' (R := R) Q).SeparatingLeft := fun x hx ↦ hB _ <| by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm
#align quadratic_form.nondegenerate_of_anisotropic QuadraticForm.separatingLeft_of_anisotropic

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [OrderedCommRing R₂] [AddCommMonoid M] [Module R₂ M]
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
variable [CommRing R] [AddCommMonoid M] [Module R M]

/-- `M.toQuadraticForm'` is the map `fun x ↦ col x * M * row x` as a quadratic form. -/
def Matrix.toQuadraticForm' (M : Matrix n n R) : QuadraticForm R (n → R) :=
  LinearMap.BilinForm.toQuadraticForm (Matrix.toLinearMap₂' M)
#align matrix.to_quadratic_form' Matrix.toQuadraticForm'

variable [Invertible (2 : R)]

/-- A matrix representation of the quadratic form. -/
def QuadraticForm.toMatrix' (Q : QuadraticForm R (n → R)) : Matrix n n R :=
  LinearMap.toMatrix₂' (associated (R := R) Q)
#align quadratic_form.to_matrix' QuadraticForm.toMatrix'

open QuadraticForm

theorem QuadraticForm.toMatrix'_smul (a : R) (Q : QuadraticForm R (n → R)) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp only [toMatrix', LinearEquiv.map_smul, LinearMap.map_smul]
#align quadratic_form.to_matrix'_smul QuadraticForm.toMatrix'_smul

theorem QuadraticForm.isSymm_toMatrix' (Q : QuadraticForm R (n → R)) : Q.toMatrix'.IsSymm := by
  ext i j
  rw [toMatrix', Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply,
    ← associated_isSymm, RingHom.id_apply, associated_apply]
#align quadratic_form.is_symm_to_matrix' QuadraticForm.isSymm_toMatrix'

end

namespace QuadraticForm

variable {n : Type w} [Fintype n]
variable [CommRing R] [DecidableEq n] [Invertible (2 : R)]
variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
theorem toMatrix'_comp (Q : QuadraticForm R (m → R)) (f : (n → R) →ₗ[R] m → R) :
    (Q.comp f).toMatrix' = (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f) := by
  ext
  simp only [QuadraticForm.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

#align quadratic_form.to_matrix'_comp QuadraticForm.toMatrix'_comp

section Discriminant

variable {Q : QuadraticForm R (n → R)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticForm R (n → R)) : R :=
  Q.toMatrix'.det
#align quadratic_form.discr QuadraticForm.discr

theorem discr_smul (a : R) : (a • Q).discr = a ^ Fintype.card n * Q.discr := by
  simp only [discr, toMatrix'_smul, Matrix.det_smul]
#align quadratic_form.discr_smul QuadraticForm.discr_smul

theorem discr_comp (f : (n → R) →ₗ[R] n → R) :
    (Q.comp f).discr = f.toMatrix'.det * f.toMatrix'.det * Q.discr := by
  simp only [Matrix.det_transpose, mul_left_comm, QuadraticForm.toMatrix'_comp, mul_comm,
    Matrix.det_mul, discr]
#align quadratic_form.discr_comp QuadraticForm.discr_comp

end Discriminant

end QuadraticForm

namespace QuadraticForm

end QuadraticForm

namespace LinearMap

namespace BilinForm

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
A bilinear form is separating left if the quadratic form it is associated with is anisotropic.
-/
theorem separatingLeft_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticForm.Anisotropic) :
    B.SeparatingLeft := fun x hx => hB _ (hx x)
#align bilin_form.nondegenerate_of_anisotropic LinearMap.BilinForm.separatingLeft_of_anisotropic

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M}
    (hB₁ : B ≠ 0) (hB₂ : B.IsSymm) : ∃ x, ¬B.IsOrtho x x := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticForm.exists_quadraticForm_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩
#align bilin_form.exists_bilin_form_self_ne_zero LinearMap.BilinForm.exists_bilinForm_self_ne_zero

open FiniteDimensional

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : BilinForm K V} (hB₂ : B.IsSymm) :
    ∃ v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v := by
  induction' hd : finrank K V with d ih generalizing V
  · exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  haveI := finrank_pos_iff.1 (hd.symm ▸ Nat.succ_pos d : 0 < finrank K V)
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := FiniteDimensional.finBasis K V
    rw [hd] at b
    exact ⟨b, fun i j _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilinForm_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_map hx)] at hd
  let B' :=  B.domRestrict₁₂ (Submodule.orthogonalBilin (K ∙ x) B )
    (Submodule.orthogonalBilin (K ∙ x) B )
  obtain ⟨v', hv₁⟩ := ih (hB₂.domRestrict _ : B'.IsSymm) (Nat.succ.inj hd)
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
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ map_zero _)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [IsOrtho, map_smul, smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hx, add_neg_self, mul_zero])
  refine ⟨b, ?_⟩
  rw [Basis.coe_mkFinCons]
  intro j i
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [IsOrtho, ← hB₂]
    exact (v' j).prop _ (Submodule.mem_span_singleton_self x)
  · exact (v' i).prop _ (Submodule.mem_span_singleton_self x)
  · exact hv₁ (ne_of_apply_ne _ hij)
#align bilin_form.exists_orthogonal_basis LinearMap.BilinForm.exists_orthogonal_basis

end BilinForm

end LinearMap

namespace QuadraticForm

open Finset

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type*}

/-- Given a quadratic form `Q` and a basis, `basisRepr` is the basis representation of `Q`. -/
noncomputable def basisRepr [Finite ι] (Q : QuadraticForm R M) (v : Basis ι R M) :
    QuadraticForm R (ι → R) :=
  Q.comp v.equivFun.symm
#align quadratic_form.basis_repr QuadraticForm.basisRepr

@[simp]
theorem basisRepr_apply [Fintype ι] {v : Basis ι R M} (Q : QuadraticForm R M) (w : ι → R) :
    Q.basisRepr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equivFun_symm_apply]
  rfl
#align quadratic_form.basis_repr_apply QuadraticForm.basisRepr_apply

variable [Fintype ι] {v : Basis ι R M}

section

variable (R)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R` or
`[Algebra S R]`, although this is stated more generally. -/
def weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    QuadraticForm R (ι → R) :=
  ∑ i : ι, w i • proj i i
#align quadratic_form.weighted_sum_squares QuadraticForm.weightedSumSquares

end

@[simp]
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι → S) (v : ι → R) :
    weightedSumSquares R w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticForm.sum_apply _ _ _
#align quadratic_form.weighted_sum_squares_apply QuadraticForm.weightedSumSquares_apply

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basisRepr_eq_of_iIsOrtho {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (2 : R)] (Q : QuadraticForm R M) (v : Basis ι R M)
    (hv₂ : (associated (R := R) Q).IsOrthoᵢ v) :
    Q.basisRepr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basisRepr_apply, ← @associated_eq_self_apply R, map_sum, weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R, LinearMap.map_sum₂, sum_eq_single_of_mem j hj]
  · rw [LinearMap.map_smul, LinearMap.map_smul₂, smul_eq_mul, associated_apply, smul_eq_mul,
      smul_eq_mul]
    ring
  · intro i _ hij
    rw [LinearMap.map_smul, LinearMap.map_smul₂,
      show associatedHom R Q (v i) (v j) = 0 from hv₂ hij, smul_eq_mul, smul_eq_mul,
      mul_zero, mul_zero]
set_option linter.uppercaseLean3 false in
#align quadratic_form.basis_repr_eq_of_is_Ortho QuadraticForm.basisRepr_eq_of_iIsOrtho

end QuadraticForm
