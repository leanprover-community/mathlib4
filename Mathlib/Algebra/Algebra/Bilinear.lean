/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.GroupPower.IterateHom
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

variable (R A : Type*) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The multiplication in a non-unital non-associative algebra is a bilinear map.

A weaker version of this for semirings exists as `AddMonoidHom.mul`. -/
def mul : A →ₗ[R] A →ₗ[R] A :=
  LinearMap.mk₂ R (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- The multiplication map on a non-unital algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
noncomputable def mul' : A ⊗[R] A →ₗ[R] A :=
  TensorProduct.lift (mul R A)

variable {A}

/-- The multiplication on the left in a non-unital algebra is a linear map. -/
def mulLeft (a : A) : A →ₗ[R] A :=
  mul R A a

/-- The multiplication on the right in an algebra is a linear map. -/
def mulRight (a : A) : A →ₗ[R] A :=
  (mul R A).flip a

/-- Simultaneous multiplication on the left and right is a linear map. -/
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]
theorem mulLeft_toAddMonoidHom (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a :=
  rfl

@[simp]
theorem mulRight_toAddMonoidHom (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a :=
  rfl

variable {R}

@[simp]
theorem mul_apply' (a b : A) : mul R A a b = a * b :=
  rfl

@[simp]
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b :=
  rfl

@[simp]
theorem mulRight_apply (a b : A) : mulRight R a b = b * a :=
  rfl

@[simp]
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

@[simp]
theorem mul'_apply {a b : A} : mul' R A (a ⊗ₜ b) = a * b :=
  rfl

@[simp]
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 :=
  (mul R A).map_zero

@[simp]
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 :=
  (mul R A).flip.map_zero

end NonUnitalNonAssoc

section NonUnital

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A]

/-- The multiplication in a non-unital algebra is a bilinear map.

A weaker version of this for non-unital non-associative algebras exists as `LinearMap.mul`. -/
def _root_.NonUnitalAlgHom.lmul : A →ₙₐ[R] End R A :=
  { mul R A with
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c
    map_zero' := by
      ext a
      exact zero_mul a }

variable {R A}

@[simp]
theorem _root_.NonUnitalAlgHom.coe_lmul_eq_mul : ⇑(NonUnitalAlgHom.lmul R A) = mul R A :=
  rfl

theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

@[simp]
theorem mulLeft_mul (a b : A) : mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]
theorem mulRight_mul (a b : A) : mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

end NonUnital

section Semiring

variable (R A B : Type*) [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {R A B} in
/-- A `LinearMap` preserves multiplication if pre- and post- composition with `LinearMap.mul` are
equivalent. By converting the statement into an equality of `LinearMap`s, this lemma allows various
specialized `ext` lemmas about `→ₗ[R]` to then be applied.

This is the `LinearMap` version of `AddMonoidHom.map_mul_iff`. -/
theorem map_mul_iff (f : A →ₗ[R] B) :
    (∀ x y, f (x * y) = f x * f y) ↔
      (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B ∘ₗ f).compl₂ f :=
  Iff.symm LinearMap.ext_iff₂

/-- The multiplication in an algebra is an algebra homomorphism into the endomorphisms on
the algebra.

A weaker version of this for non-unital algebras exists as `NonUnitalAlgHom.mul`. -/
def _root_.Algebra.lmul : A →ₐ[R] End R A :=
  { LinearMap.mul R A with
    map_one' := by
      ext a
      exact one_mul a
    map_mul' := by
      intro a b
      ext c
      exact mul_assoc a b c
    map_zero' := by
      ext a
      exact zero_mul a
    commutes' := by
      intro r
      ext a
      exact (Algebra.smul_def r a).symm }

variable {R A}

@[simp]
theorem _root_.Algebra.coe_lmul_eq_mul : ⇑(Algebra.lmul R A) = mul R A :=
  rfl

theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) :=
  fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1

theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End_isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

@[simp]
theorem mulLeft_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  -- Porting note: had to supply `R` explicitly in `@mulLeft_apply` below
  · rw [← mul_one a, ← @mulLeft_apply R _ _ _ _ _ _ a 1, h, LinearMap.zero_apply]
  · rw [h]
    exact mulLeft_zero_eq_zero

@[simp]
theorem mulRight_eq_zero_iff (a : A) : mulRight R a = 0 ↔ a = 0 := by
  constructor <;> intro h
  -- Porting note: had to supply `R` explicitly in `@mulRight_apply` below
  · rw [← one_mul a, ← @mulRight_apply R _ _ _ _ _ _ a 1, h, LinearMap.zero_apply]
  · rw [h]
    exact mulRight_zero_eq_zero

@[simp]
theorem mulLeft_one : mulLeft R (1 : A) = LinearMap.id := by
  ext
  simp

@[simp]
theorem mulRight_one : mulRight R (1 : A) = LinearMap.id := by
  ext
  simp

@[simp]
theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) := by
  simpa only [mulLeft, ← Algebra.coe_lmul_eq_mul] using (map_pow (Algebra.lmul R A) a n).symm

@[simp]
theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) := by
  simp only [mulRight, ← Algebra.coe_lmul_eq_mul]
  exact
    LinearMap.coe_injective (((mulRight R a).coe_pow n).symm ▸ mul_right_iterate a n)

theorem toSpanSingleton_eq_algebra_linearMap : toSpanSingleton R A 1 = Algebra.linearMap R A := by
  ext; simp

end Semiring

section Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

theorem mulLeft_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) :
    Function.Injective (mulLeft R x) := by
  letI : Nontrivial A := ⟨⟨x, 0, hx⟩⟩
  letI := NoZeroDivisors.to_isDomain A
  exact mul_right_injective₀ hx

theorem mulRight_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) :
    Function.Injective (mulRight R x) := by
  letI : Nontrivial A := ⟨⟨x, 0, hx⟩⟩
  letI := NoZeroDivisors.to_isDomain A
  exact mul_left_injective₀ hx

theorem mul_injective [NoZeroDivisors A] {x : A} (hx : x ≠ 0) : Function.Injective (mul R A x) := by
  letI : Nontrivial A := ⟨⟨x, 0, hx⟩⟩
  letI := NoZeroDivisors.to_isDomain A
  exact mul_right_injective₀ hx

end Ring

end LinearMap
