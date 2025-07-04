/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# The coalgebra structure on monoid algebras

Given a type `X`, a commutative semiring `R` and a semiring `A` which is also an `R`-coalgebra,
this file collects results about the `R`-coalgebra instance on `A[X]` inherited from the
corresponding structure on its coefficients, defined in `Mathlib/RingTheory/Coalgebra/Basic.lean`.

## Main definitions

* `(Add)MonoidAlgebra.instCoalgebra`: the `R`-coalgebra structure on `A[X]` when `A` is an
  `R`-coalgebra.
* `LaurentPolynomial.instCoalgebra`: the `R`-coalgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-coalgebra.
-/

noncomputable section

open Coalgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Module R A] [Coalgebra R A]

variable (R A X) in
instance instCoalgebra : Coalgebra R (MonoidAlgebra A X) := Finsupp.instCoalgebra R X A

instance instIsCocomm [IsCocomm R A] : IsCocomm R (MonoidAlgebra A X) := Finsupp.instIsCocomm R X A

@[simp]
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[simp]
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (R := R) (single x a) =
      TensorProduct.map (lsingle x) (lsingle x) (Coalgebra.comul a) :=
  Finsupp.comul_single _ _ _ _ _

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Module R A] [Coalgebra R A]

variable (R A X) in
instance instCoalgebra : Coalgebra R A[X] := Finsupp.instCoalgebra R X A

instance instIsCocomm [IsCocomm R A] : IsCocomm R A[X] := Finsupp.instIsCocomm R X A

@[simp]
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[simp]
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (R := R) (single x a) =
      TensorProduct.map (lsingle x) (lsingle x) (Coalgebra.comul a) :=
  Finsupp.comul_single _ _ _ _ _

end AddMonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Module R A] [Coalgebra R A]

instance instCoalgebra : Coalgebra R A[T;T⁻¹] := inferInstanceAs <| Coalgebra R A[ℤ]

instance instIsCocomm [IsCocomm R A] : IsCocomm R A[T;T⁻¹] := inferInstanceAs <| IsCocomm R A[ℤ]

variable {R A}

@[simp]
theorem comul_C (a : A) :
    Coalgebra.comul (R := R) (C a) =
      TensorProduct.map (lsingle 0) (lsingle 0) (Coalgebra.comul (R := R) a) :=
  comul_single _ _

@[simp]
theorem comul_C_mul_T (a : A) (n : ℤ) :
    Coalgebra.comul (R := R) (C a * T n) =
      TensorProduct.map (lsingle n) (lsingle n) (Coalgebra.comul (R := R) a) := by
  simp [← single_eq_C_mul_T]

theorem comul_C_mul_T_self (a : R) (n : ℤ) :
    Coalgebra.comul (C a * T n) = T n ⊗ₜ[R] (C a * T n) := by
  simp

@[simp]
theorem counit_C (a : A) :
    Coalgebra.counit (R := R) (C a) = Coalgebra.counit (R := R) a :=
  counit_single _ _

@[simp]
theorem counit_C_mul_T (a : A) (n : ℤ) :
    Coalgebra.counit (R := R) (C a * T n) = Coalgebra.counit (R := R) a := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial
