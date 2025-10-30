/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.NoncommRing

/-! # Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`opRingEquiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/


open Polynomial

open MulOpposite

variable {R : Type*} [Semiring R]

noncomputable section

namespace Polynomial

/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a polynomial
to the corresponding element of the opposite ring. -/
def opRingEquiv (R : Type*) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans AddMonoidAlgebra.opRingEquiv).trans (toFinsuppIso _).symm

/-!  Lemmas to get started, using `opRingEquiv R` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


@[simp]
theorem opRingEquiv_op_monomial (n : ℕ) (r : R) :
    opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r) := by
  simp only [opRingEquiv, RingEquiv.coe_trans, Function.comp_apply,
    AddMonoidAlgebra.opRingEquiv_apply, RingEquiv.op_apply_apply, toFinsuppIso_apply, unop_op,
    toFinsupp_monomial, Finsupp.mapRange_single, toFinsuppIso_symm_apply, ofFinsupp_single]

@[simp]
theorem opRingEquiv_op_C (a : R) : opRingEquiv R (op (C a)) = C (op a) :=
  opRingEquiv_op_monomial 0 a

@[simp]
theorem opRingEquiv_op_X : opRingEquiv R (op (X : R[X])) = X :=
  opRingEquiv_op_monomial 1 1

theorem opRingEquiv_op_C_mul_X_pow (r : R) (n : ℕ) :
    opRingEquiv R (op (C r * X ^ n : R[X])) = C (op r) * X ^ n := by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, opRingEquiv_op_X, opRingEquiv_op_C]

/-!  Lemmas to get started, using `(opRingEquiv R).symm` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


@[simp]
theorem opRingEquiv_symm_monomial (n : ℕ) (r : Rᵐᵒᵖ) :
    (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r)) :=
  (opRingEquiv R).injective (by simp)

@[simp]
theorem opRingEquiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (C a) = op (C (unop a)) :=
  opRingEquiv_symm_monomial 0 a

@[simp]
theorem opRingEquiv_symm_X : (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X :=
  opRingEquiv_symm_monomial 1 1

theorem opRingEquiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R).symm (C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial, opRingEquiv_symm_monomial, C_mul_X_pow_eq_monomial]

/-!  Lemmas about more global properties of polynomials and opposites. -/


@[simp]
theorem coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R p).coeff n = op ((unop p).coeff n) := rfl

@[simp]
theorem support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).support = (unop p).support :=
  Finsupp.support_mapRange_of_injective (map_zero _) _ op_injective

@[simp]
theorem natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop p).natDegree := by
  by_cases p0 : p = 0
  · simp only [p0, map_zero, natDegree_zero, unop_zero]
  · simp only [p0, natDegree_eq_support_max', Ne, EmbeddingLike.map_eq_zero_iff, not_false_iff,
      support_opRingEquiv, unop_eq_zero_iff]

@[simp]
theorem leadingCoeff_opRingEquiv (p : R[X]ᵐᵒᵖ) :
    (opRingEquiv R p).leadingCoeff = op (unop p).leadingCoeff := by
  rw [leadingCoeff, coeff_opRingEquiv, natDegree_opRingEquiv, leadingCoeff]

theorem isLeftCancelMulZero_iff :
    IsLeftCancelMulZero R[X] ↔ IsLeftCancelMulZero R ∧ IsCancelAdd R where
  mp h := .intro (C_injective.isLeftCancelMulZero _ C_0 fun _ _ ↦ C_mul) <|
    have : IsLeftCancelAdd R := .mk fun a b c eq ↦ by
      nontriviality R
      let trinomial (r : R) : R[X] := a • X ^ 2 + r • X + C a
      have ht r : (X + C 1) * trinomial r = a • X ^ 3 + (a + r) • X ^ 2 + (a + r) • X + C a := by
        simp only [trinomial, mul_add, add_mul, ← C_mul', C_1, one_mul, ← mul_assoc, X_mul_C, C_add]
        noncomm_ring
      simpa [trinomial] using congr_arg (coeff · 1) <|
        h.1 (a₁ := trinomial b) (a₂ := trinomial c) (X_add_C_ne_zero 1) <| by simp_rw [ht, eq]
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd R
  mpr := fun ⟨_, _⟩ ↦ inferInstance

theorem isRightCancelMulZero_iff :
    IsRightCancelMulZero R[X] ↔ IsRightCancelMulZero R ∧ IsCancelAdd R := by
  rw [← MulOpposite.isLeftCancelMulZero_iff, (opRingEquiv R).isLeftCancelMulZero_iff,
    isLeftCancelMulZero_iff, MulOpposite.isLeftCancelMulZero_iff, MulOpposite.isCancelAdd_iff]

protected theorem isCancelMulZero_iff :
    IsCancelMulZero R[X] ↔ IsCancelMulZero R ∧ IsCancelAdd R := by
  simp_rw [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff]
  rw [and_and_and_comm, and_self]

theorem isDomain_iff : IsDomain R[X] ↔ IsDomain R ∧ IsCancelAdd R := by
  simp_rw [isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff,
    Polynomial.isCancelMulZero_iff, and_right_comm]

end Polynomial
