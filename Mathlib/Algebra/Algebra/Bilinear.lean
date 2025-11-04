/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `Algebra.Algebra.Basic`,
in order to avoid importing `LinearAlgebra.BilinearMap` and
`LinearAlgebra.TensorProduct` unnecessarily.
-/

open TensorProduct Module

namespace LinearMap

section NonUnitalNonAssoc
variable (R A : Type*)

section one_side
variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable {A} [SMulCommClass R A A]

/-- The multiplication on the left in an algebra is a linear map.

Note that this only assumes `SMulCommClass R A A`, so that it also works for `R := Aᵐᵒᵖ`.

When `A` is unital and associative, this is the same as `DistribMulAction.toLinearMap R A a` -/
def mulLeft (a : A) : A →ₗ[R] A where
  toFun := (a * ·)
  map_add' := mul_add _
  map_smul' _ := mul_smul_comm _ _

@[simp]
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := rfl

@[simp]
theorem mulLeft_toAddMonoidHom (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a := rfl

variable (A) in
@[simp]
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := ext fun _ => zero_mul _

end left

section right
variable {A} [IsScalarTower R A A]

/-- The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R := A`.

When `A` is unital and associative, this is the same as
`DistribMulAction.toLinearMap R A (MulOpposite.op b)`. -/
def mulRight (b : A) : A →ₗ[R] A where
  toFun := (· * b)
  map_add' _ _ := add_mul _ _ _
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]
theorem mulRight_apply (a b : A) : mulRight R a b = b * a := rfl

@[simp]
theorem mulRight_toAddMonoidHom (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a := rfl

variable (A) in
@[simp]
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := ext fun _ => mul_zero _

end right

end one_side

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
-- TODO: upgrade to A-linear map if A is a semiring.
def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

variable {A}

/-- Simultaneous multiplication on the left and right is a linear map. -/
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

variable {R}

@[simp]
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl

@[simp]
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

@[simp]
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
  rfl

variable {M : Type*} [AddCommMonoid M] [Module R M]

theorem lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} :
    lift (lsmul R M ∘ₗ mul R R r) = lsmul R M r ∘ₗ lift (lsmul R M) := by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

end NonUnitalNonAssoc

section NonUnital
variable (R A B : Type*)

section one_side
variable [Semiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

@[simp]
theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]
theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

end one_side

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]

/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `LinearMap.mul`. -/
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

variable {R A B}

@[simp]
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl

theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

/-- A `LinearMap` preserves multiplication if pre- and post- composition with `LinearMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this lemma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`. -/
theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f :=
  Iff.symm LinearMap.ext_iff₂

end NonUnital

section Injective
variable {R A : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]

@[simp] lemma mulLeft_inj [SMulCommClass R A A] {a b : A} :
    mulLeft R a = mulLeft R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

@[simp] lemma mulRight_inj [IsScalarTower R A A] {a b : A} :
    mulRight R a = mulRight R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

end Injective

section Semiring

variable (R A : Type*)
section one_side
variable [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

@[simp]
theorem mulLeft_one : mulLeft R (1 : A) = LinearMap.id := ext fun _ => one_mul _

@[simp]
theorem mulLeft_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0 :=
  mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

end left

section right
variable [Module R A] [IsScalarTower R A A]

@[simp]
theorem mulRight_one : mulRight R (1 : A) = LinearMap.id := ext fun _ => mul_one _

@[simp]
theorem mulRight_eq_zero_iff (a : A) : mulRight R a = 0 ↔ a = 0 :=
  mulRight_zero_eq_zero R A ▸ mulRight_inj

@[simp]
theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

end right

end one_side

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `NonUnitalAlgHom.lmul`. -/
def _root_.Algebra.lmul : A →ₐ[R] End R A where
  __ := NonUnitalAlgHom.lmul R A
  map_one' := mulLeft_one _ _
  commutes' r := ext fun a => (Algebra.smul_def r a).symm

variable {R A}

@[simp]
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl

theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1

theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End.isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

theorem toSpanSingleton_eq_algebra_linearMap : toSpanSingleton R A 1 = Algebra.linearMap R A := by
  ext; simp

end Semiring

end LinearMap
