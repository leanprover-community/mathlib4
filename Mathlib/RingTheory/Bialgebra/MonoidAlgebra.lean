/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The bialgebra structure on monoid algebras

Given a monoid `X`, a commutative semiring `R` and an `R`-bialgebra `A`, this file collects results
about the `R`-bialgebra instance on `A[X]` inherited from the corresponding structure on its
coefficients, building upon results in `Mathlib/RingTheory/Coalgebra/MonoidAlgebra.lean` about the
coalgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instBialgebra`: the `R`-bialgebra structure on `A[X]` when `X` is an (add)
  monoid and `A` is an `R`-bialgebra.
* `LaurentPolynomial.instBialgebra`: the `R`-bialgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-bialgebra.
-/

suppress_compilation

open Bialgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Bialgebra R A] [Monoid X]

variable (R A X) in
instance instBialgebra : Bialgebra R (MonoidAlgebra A X) where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coeFn_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Bialgebra R A] [AddMonoid X]

variable (R A X) in
instance instBialgebra : Bialgebra R A[X] where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp [single_mul_single]
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coeFn_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

end AddMonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

instance instBialgebra : Bialgebra R A[T;T⁻¹] :=
  inferInstanceAs <| Bialgebra R A[ℤ]

@[simp]
theorem comul_T (n : ℤ) :
    Coalgebra.comul (R := R) (T n : A[T;T⁻¹]) = T n ⊗ₜ[R] T n := by
  simp [T, -single_eq_C_mul_T, Algebra.TensorProduct.one_def]

@[simp]
theorem counit_T (n : ℤ) :
    Coalgebra.counit (R := R) (T n : A[T;T⁻¹]) = 1 := by
  simp [T, -single_eq_C_mul_T]

end LaurentPolynomial
