/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra structure on group algebras

Given a group `G`, a commutative semiring `R` and an `R`-Hopf algebra `A`, this file collects
results about the `R`-Hopf algebra instance on `A[G]`, building upon results in
`Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean` about the bialgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instHopfAlgebra`: the `R`-Hopf algebra structure on `A[G]` when `G` is an
  (add) group and `A` is an `R`-Hopf algebra.
* `LaurentPolynomial.instHopfAlgebra`: the `R`-Hopf algebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-Hopf algebra. When `A = R` this corresponds to the fact that `𝔾ₘ/R`
  is a group scheme.
-/

public section

noncomputable section

open HopfAlgebra

namespace MonoidAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type*} [Group G]

variable (R A G) in
set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R)]
instance instHopfAlgebraStruct : HopfAlgebraStruct R A[G] where
  antipode := Finsupp.lsum R (fun g ↦ lsingle g⁻¹ ∘ₗ antipode R) ∘ₗ (coeffLinearEquiv _).toLinearMap

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
lemma antipode_single (g : G) (a : A) : antipode R (single g a) = single g⁻¹ (antipode R a) := by
  simp [antipode]

open Coalgebra in
@[to_additive (dont_translate := R A)]
instance instHopfAlgebra : HopfAlgebra R A[G] where
  mul_antipode_rTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
      $(sum_antipode_mul_eq_algebraMap_counit (ℛ R b)))
  mul_antipode_lTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
      $(sum_mul_antipode_eq_algebraMap_counit (ℛ R b)))

end MonoidAlgebra

namespace LaurentPolynomial

open Finsupp

variable (R A : Type*) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

instance instHopfAlgebra : HopfAlgebra R A[T;T⁻¹] :=
  inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A ℤ)

variable {R A}

@[simp]
theorem antipode_C (a : A) :
    HopfAlgebra.antipode R (C a) = C (HopfAlgebra.antipode R a) := by
  rw [← single_eq_C, AddMonoidAlgebra.antipode_single]
  simp

@[simp]
theorem antipode_T (n : ℤ) :
    HopfAlgebra.antipode R (T n : A[T;T⁻¹]) = T (-n) := by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]
theorem antipode_C_mul_T (a : A) (n : ℤ) :
    HopfAlgebra.antipode R (C a * T n) = C (HopfAlgebra.antipode R a) * T (-n) := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial
