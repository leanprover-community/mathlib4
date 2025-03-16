/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of polynomial algebras

Given `[CommSemiring R] [Semiring A] [Algebra R A]` we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/

-- This file should not become entangled with `RingTheory/MatrixAlgebra`.
assert_not_exists Matrix

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

namespace PolyEquivTensor

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap

theorem toFunBilinear_apply_apply (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • (aeval X) p := rfl

@[simp] theorem toFunBilinear_apply_eq_smul (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • p.map (algebraMap R A) := rfl

theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.sum fun n r ↦ monomial n (a * algebraMap R A r) := by
  conv_lhs => rw [toFunBilinear_apply_eq_smul, ← p.sum_monomial_eq, sum, Polynomial.map_sum]
  simp [Finset.smul_sum, sum, ← smul_eq_mul]

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a linear map.
-/
def toFunLinear : A ⊗[R] R[X] →ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)

@[simp]
theorem toFunLinear_tmul_apply (a : A) (p : R[X]) :
    toFunLinear R A (a ⊗ₜ[R] p) = toFunBilinear R A a p :=
  rfl

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
theorem toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : ℕ) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 =
    a * (algebraMap R A) (coeff p k) := by classical split_ifs <;> simp [*]

theorem toFunLinear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.antidiagonal k).sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) := by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, RingHom.map_mul]

theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) := by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, mul_ite,
      mul_zero, ite_mul, zero_mul]
    simp_rw [← ite_zero_mul (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [← mul_ite_zero (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [toFunLinear_mul_tmul_mul_aux_1, toFunLinear_mul_tmul_mul_aux_2]

theorem toFunLinear_one_tmul_one :
    toFunLinear R A (1 ⊗ₜ[R] 1) = 1 := by
  rw [toFunLinear_tmul_apply, toFunBilinear_apply_apply, Polynomial.aeval_one, one_smul]

/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)

@[simp] theorem toFunAlgHom_apply_tmul_eq_smul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = a • p.map (algebraMap R A) := rfl

theorem toFunAlgHom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = p.sum fun n r => monomial n (a * (algebraMap R A) r) :=
  toFunBilinear_apply_eq_sum R A _ _

/-- (Implementation detail.)

The bare function `A[X] → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X]))

@[simp]
theorem invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [invFun, eval₂_add]

theorem invFun_monomial (n : ℕ) (a : A) :
    invFun R A (monomial n a) = (a ⊗ₜ[R] 1) * 1 ⊗ₜ[R] X ^ n :=
  eval₂_monomial _ _

theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul, eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    simp only [Algebra.smul_def]
    rfl
  · intro p q hp hq
    simp only [map_add, invFun_add, hp, hq]

theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, map_add, hp, hq]
  · intro n a
    rw [invFun_monomial, Algebra.TensorProduct.tmul_pow,
        one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, toFunAlgHom_apply_tmul,
        X_pow_eq_monomial, sum_monomial_index] <;>
      simp

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ A[X]`.
-/
def equiv : A ⊗[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

end PolyEquivTensor

open PolyEquivTensor

/-- The `R`-algebra isomorphism `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/
def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]
theorem polyEquivTensor_apply (p : A[X]) :
    polyEquivTensor R A p =
      p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X])) :=
  rfl

@[simp]
theorem polyEquivTensor_symm_apply_tmul_eq_smul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = a • p.map (algebraMap R A) := rfl

theorem polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = p.sum fun n r => monomial n (a * algebraMap R A r) :=
  toFunAlgHom_apply_tmul _ _ _ _

section

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The `A`-algebra isomorphism `A[X] ≃ₐ[A] A ⊗[R] R[X]` (when `A` is commutative). -/
def polyEquivTensor' : A[X] ≃ₐ[A] A ⊗[R] R[X] where
  __ := polyEquivTensor R A
  commutes' a := by simp

/-- `polyEquivTensor' R A` is the same as `polyEquivTensor R A` as a function. -/
@[simp] theorem coe_polyEquivTensor' : ⇑(polyEquivTensor' R A) = polyEquivTensor R A := rfl

@[simp] theorem coe_polyEquivTensor'_symm :
    ⇑(polyEquivTensor' R A).symm = (polyEquivTensor R A).symm := rfl

end

/-- If `A` is an `R`-algebra, then `A[X]` is an `R[X]` algebra.
This gives a diamond for `Algebra R[X] R[X][X]`, so this is not a global instance. -/
@[reducible] def Polynomial.algebra : Algebra R[X] A[X] :=
  (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ ↦ by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]

attribute [local instance] Polynomial.algebra

@[simp]
theorem Polynomial.algebraMap_def : algebraMap R[X] A[X] = mapRingHom (algebraMap R A) := rfl

instance : IsScalarTower R R[X] A[X] := .of_algebraMap_eq' (mapRingHom_comp_C _).symm

instance [FaithfulSMul R A] : FaithfulSMul R[X] A[X] :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

variable {S : Type*} [CommSemiring S] [Algebra R S]

instance : Algebra.IsPushout R S R[X] S[X] where
  out := .of_equiv (polyEquivTensor' R S).symm fun _ ↦
    (polyEquivTensor_symm_apply_tmul_eq_smul ..).trans <| one_smul ..

instance : Algebra.IsPushout R R[X] S S[X] := .symm inferInstance
