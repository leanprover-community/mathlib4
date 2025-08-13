/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic functions

This file defines algebraic functions as the image of the `algebraMap R[X] (R → S)`.
-/

assert_not_exists IsIntegralClosure LinearIndependent IsLocalRing MvPolynomial

open Polynomial

section Pi

variable (R S T : Type*)

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
def Polynomial.hasSMulPi [Semiring R] [SMul R S] : SMul R[X] (R → S) :=
  ⟨fun p f x => eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R] [Semiring S] [Algebra R S]
    [SMul S T] : SMul R[X] (S → T) :=
  ⟨fun p f x => aeval x p • f x⟩

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
theorem polynomial_smul_apply [Semiring R] [SMul R S] (p : R[X]) (f : R → S) (x : R) :
    (p • f) x = eval x p • f x :=
  rfl

@[simp]
theorem polynomial_smul_apply' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
    (p : R[X]) (f : S → T) (x : S) : (p • f) x = aeval x p • f x :=
  rfl

variable [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T]

-- Porting note: the proofs in this definition used `funext` in term-mode, but I was not able
-- to get them to work anymore.
/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
noncomputable def Polynomial.algebraPi : Algebra R[X] (S → T) where
  __ := Polynomial.hasSMulPi' R S T
  algebraMap :=
  { toFun := fun p z => algebraMap S T (aeval z p)
    map_one' := by
      funext z
      simp only [Pi.one_apply, map_one]
    map_mul' := fun f g => by
      funext z
      simp only [Pi.mul_apply, map_mul]
    map_zero' := by
      funext z
      simp only [Pi.zero_apply, map_zero]
    map_add' := fun f g => by
      funext z
      simp only [Pi.add_apply, map_add] }
  commutes' := fun p f => by
    funext z
    exact mul_comm _ _
  smul_def' := fun p f => by
    funext z
    simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul]

attribute [local instance] Polynomial.algebraPi

@[simp]
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R[X] (S → T) : R[X] → S → T) = fun p z => algebraMap _ _ (aeval z p) :=
  rfl

@[simp]
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R[X] (R → R) : R[X] → R → R) = fun p z => eval z p :=
  rfl

end Pi
