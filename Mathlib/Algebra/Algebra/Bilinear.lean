/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Facts about algebras involving bilinear maps and tensor products

We move a few basic statements about algebras out of `Algebra.Algebra.Basic`,
in order to avoid importing `LinearAlgebra.BilinearMap` and
`LinearAlgebra.TensorProduct` unnecessarily.
-/

@[expose] public section

open TensorProduct Module

variable {R A B : Type*}

namespace LinearMap

section NonUnitalNonAssoc

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
@[simps!]
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ" => LinearMap.mul' _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "μ[" R "]" => LinearMap.mul' R _

variable {A R}

@[simp]
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
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

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]
variable [SMulCommClass R A A] [IsScalarTower R A A]
variable [SMulCommClass R B B] [IsScalarTower R B B]

variable (R A) in
/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `LinearMap.mul`. -/
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A where
  __ := mul R A
  map_mul' := mulLeft_mul _ _
  map_zero' := mulLeft_zero_eq_zero _ _

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

section Semiring

variable (R A)
section one_side
variable [Semiring R] [Semiring A]

section left
variable [Module R A] [SMulCommClass R A A]

@[simp]
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) :=
  match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

end left

section right
variable [Module R A] [IsScalarTower R A A]

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

theorem toSpanSingleton_one_eq_algebraLinearMap :
    toSpanSingleton R A 1 = Algebra.linearMap R A := by ext; simp

@[deprecated (since := "2025-12-30")] alias toSpanSingleton_eq_algebra_linearMap :=
  toSpanSingleton_one_eq_algebraLinearMap

variable (R A) in
/-- The multiplication map on an `R`-algebra, as an `A`-linear map from `A ⊗[R] A` to `A`. -/
@[simps!] def mul'' : A ⊗[R] A →ₗ[A] A where
  __ := mul' R A
  map_smul' a x := x.induction_on (by simp) (by simp +contextual [mul', smul_tmul', mul_assoc])
    (by simp +contextual [mul_add])

end Semiring

section CommSemiring
-- TODO: Generalise to `NonUnitalNonAssocCommSemiring`. This can't currently be done
-- because there is no instance **to** `NonUnitalNonAssocCommSemiring`.
variable [CommSemiring R] [NonUnitalCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

@[simp] lemma flip_mul : (mul R A).flip = mul R A := by ext; simp [mul_comm]

lemma mul'_comp_comm : mul' R A ∘ₗ TensorProduct.comm R A A = mul' R A := by
  simp [mul', lift_comp_comm_eq]

lemma mul'_comm (x : A ⊗[R] A) : mul' R A (TensorProduct.comm R A A x) = mul' R A x :=
  congr($mul'_comp_comm _)

end CommSemiring
end LinearMap

open scoped RingTheory.LinearMap

namespace NonUnitalAlgHom
variable [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

lemma comp_mul' (f : A →ₙₐ[R] B) : (f : A →ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f ⊗ₘ f) :=
  TensorProduct.ext' <| by simp

end NonUnitalAlgHom

namespace AlgHom
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

lemma comp_mul' (f : A →ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
  TensorProduct.ext' <| by simp

end AlgHom
