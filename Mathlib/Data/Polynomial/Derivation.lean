/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard Hill
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Polynomial.AlgebraMap

/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

namespace Polynomial

open scoped BigOperators

noncomputable section

variable {R A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

section

@[simp]
theorem derivation_C (D : Derivation R (Polynomial R) A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

-- simp normal form is `derivation_C_mul'`
theorem derivation_C_mul (D : Derivation R (Polynomial R) A) (a : R) (f : Polynomial R) :
    D (C a * f) = a • D f := by rw [C_mul', D.map_smul]

@[simp]
theorem derivation_C_mul' (D : Derivation R (Polynomial R) A) (a : R) (f : Polynomial R) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this, derivation_C_mul]

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (Polynomial R) A} (h : D₁ X = D₂ X) : D₁ = D₂ :=
  Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) (mem_adjoin_X f)

variable [IsScalarTower R (Polynomial R) A]

variable (R)

/-- The derivation on `R[X]` that takes the value `a` on `X`. -/
def mkDerivation (a : A) : Derivation R (Polynomial R) A where
  toLinearMap := (LinearMap.restrictScalars R <| LinearMap.toSpanSingleton R[X] A a).comp derivative
  map_one_eq_zero' := by simp
  leibniz' := by
    intros f g
    simp [mul_comm, mul_smul, add_comm]

@[simp]
theorem mkDerivation_X (a : A) : mkDerivation R a X = a := by simp [mkDerivation]

/-- `Polynomial.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }
