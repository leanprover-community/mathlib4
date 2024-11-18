/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Polynomial.Defs

/-!
# Module structure on univariate polynomials

## Main definitions

* `Polynomial.module`: module structure on `Polynomial`
-/

noncomputable section

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

/-! ### Conversions to and from `AddMonoidAlgebra`

Since `R[X]` is not defeq to `R[ℕ]`, but instead is a structure wrapping
it, we have to copy across all the arithmetic operators manually, along with the lemmas about how
they unfold around `Polynomial.ofFinsupp` and `Polynomial.toFinsupp`.
-/


section AddMonoidAlgebra

theorem _root_.IsSMulRegular.polynomial {S : Type*} [Monoid S] [DistribMulAction S R] {a : S}
    (ha : IsSMulRegular R a) : IsSMulRegular R[X] a
  | ⟨_x⟩, ⟨_y⟩, h => congr_arg _ <| ha.finsupp (Polynomial.ofFinsupp.inj h)

instance distribSMul {S} [DistribSMul S R] : DistribSMul S R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { Function.Injective.distribSMul ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_injective
      toFinsupp_smul with
    toSMulZeroClass := Polynomial.smulZeroClass }

instance distribMulAction {S} [Monoid S] [DistribMulAction S R] : DistribMulAction S R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { Function.Injective.distribMulAction ⟨⟨toFinsupp, toFinsupp_zero (R := R)⟩, toFinsupp_add⟩
      toFinsupp_injective toFinsupp_smul with
    toSMul := Polynomial.smulZeroClass.toSMul }

instance faithfulSMul {S} [SMulZeroClass S R] [FaithfulSMul S R] : FaithfulSMul S R[X] where
  eq_of_smul_eq_smul {_s₁ _s₂} h :=
    eq_of_smul_eq_smul fun a : ℕ →₀ R => congr_arg toFinsupp (h ⟨a⟩)

instance module {S} [Semiring S] [Module S R] : Module S R[X] :=
  --TODO: add reference to library note in PR https://github.com/leanprover-community/mathlib4/pull/7432
  { Function.Injective.module _ ⟨⟨toFinsupp, toFinsupp_zero⟩, toFinsupp_add⟩ toFinsupp_injective
      toFinsupp_smul with
    toDistribMulAction := Polynomial.distribMulAction }

instance smulCommClass {S₁ S₂} [SMulZeroClass S₁ R] [SMulZeroClass S₂ R] [SMulCommClass S₁ S₂ R] :
  SMulCommClass S₁ S₂ R[X] :=
  ⟨by
    rintro m n ⟨f⟩
    simp_rw [← ofFinsupp_smul, smul_comm m n f]⟩

instance isScalarTower {S₁ S₂} [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
  [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ R[X] :=
  ⟨by
    rintro _ _ ⟨⟩
    simp_rw [← ofFinsupp_smul, smul_assoc]⟩

instance isScalarTower_right {α K : Type*} [Semiring K] [DistribSMul α K] [IsScalarTower α K K] :
    IsScalarTower α K[X] K[X] :=
  ⟨by
    rintro _ ⟨⟩ ⟨⟩
    simp_rw [smul_eq_mul, ← ofFinsupp_smul, ← ofFinsupp_mul, ← ofFinsupp_smul, smul_mul_assoc]⟩

instance isCentralScalar {S} [SMulZeroClass S R] [SMulZeroClass Sᵐᵒᵖ R] [IsCentralScalar S R] :
  IsCentralScalar S R[X] :=
  ⟨by
    rintro _ ⟨⟩
    simp_rw [← ofFinsupp_smul, op_smul_eq_smul]⟩

instance unique [Subsingleton R] : Unique R[X] :=
  { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      apply congr_arg ofFinsupp
      simp [eq_iff_true_of_subsingleton] }

variable (R)

end AddMonoidAlgebra

end Semiring

end Polynomial
