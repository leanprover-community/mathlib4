/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Monomial

/-!
# Algebra structure of the polynomial ring

We show that `A[X]` is an R-algebra when `A` is an R-algebra.

## Main definitions
* `Polynomial.algebraOfAlgebra`: lift `R`-algebra structure on `A` to `A[X]`.

## Main results
* `Polynomial.algHom_ext'`: `R`-algebra maps out of `A[X]` that agree on constants and `X`,
  agree everywhere.
* `Polynomial.algHom_ext`: `R`-algebra maps out of `R[X]` that agree on `X`, agree everywhere.
-/

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {p q r : R[X]}

/-- Note that this instance also provides `Algebra R R[X]`. -/
instance algebraOfAlgebra : Algebra R A[X] where
  smul_def' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert Algebra.commutes' r p.toFinsupp
  toRingHom := C.comp (algebraMap R A)

@[simp]
theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl

@[simp]
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl

theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  rfl

@[simp]
theorem algebraMap_eq : algebraMap R R[X] = C :=
  rfl

/-- `Polynomial.C` as an `AlgHom`. -/
@[simps! apply]
def CAlgHom : A →ₐ[R] A[X] where
  toRingHom := C
  commutes' _ := rfl

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
theorem algHom_ext' {f g : A[X] →ₐ[R] B}
    (hC : f.comp CAlgHom = g.comp CAlgHom)
    (hX : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

@[ext 1200]
theorem algHom_ext {f g : R[X] →ₐ[R] B} (hX : f X = g X) :
    f = g :=
  algHom_ext' (Subsingleton.elim _ _) hX

variable (R)

open AddMonoidAlgebra in
/-- Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
def toFinsuppIsoAlg : R[X] ≃ₐ[R] R[ℕ] :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

end CommSemiring

end Polynomial
