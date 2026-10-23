/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots

/-!
# Roots of Laurent polynomials

Let `S` be an `R`-algebra such that `IsDomain S` and `FaithfulSMul R S`.  Then a Laurent polynomial
over `R` is determined by its values at the units of `S`, as soon as there are infinitely many of
them: this is the analogue for `R[T;T⁻¹]` of `Polynomial.eq_zero_of_infinite_isRoot`.

## Main results

* `LaurentPolynomial.eq_zero_of_infinite_eval₂_eq_zero`: a Laurent polynomial vanishing at
  infinitely many units is zero.
* `LaurentPolynomial.eq_of_infinite_eval₂_eq`: two Laurent polynomials agreeing at infinitely
  many units are equal.
-/

@[expose] public section

namespace LaurentPolynomial

variable {R S : Type*} [CommRing S] [IsDomain S]

/-- A Laurent polynomial over a domain `S` vanishing at infinitely many units of `S` is zero. -/
theorem eq_zero_of_infinite_eval₂_id_eq_zero (p : S[T;T⁻¹])
    (h : {x : Sˣ | eval₂ (RingHom.id S) x p = 0}.Infinite) : p = 0 := by
  obtain ⟨n, q, hq⟩ := exists_T_pow p
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injOn_mapsTo Units.val_injective.injOn (fun x hx ↦ ?_) h)
    simpa [hx.out] using congr(eval₂ (RingHom.id S) x $hq)
  rw [hq0, map_zero] at hq
  exact (isUnit_T (n : ℤ)).mul_left_eq_zero.mp hq.symm

/-- Two Laurent polynomials over a domain `S` agreeing at infinitely many units of `S` are
equal. -/
theorem eq_of_infinite_eval₂_id_eq {p q : S[T;T⁻¹]}
    (h : {x : Sˣ | eval₂ (RingHom.id S) x p = eval₂ (RingHom.id S) x q}.Infinite) : p = q :=
  sub_eq_zero.mp <| eq_zero_of_infinite_eval₂_id_eq_zero _ <| by simpa [sub_eq_zero] using h

/-- Two Laurent polynomials agreeing at infinitely many units are equal. -/
theorem eq_of_infinite_eval₂_eq [CommSemiring R] [Algebra R S] [FaithfulSMul R S]
    {p q : R[T;T⁻¹]}
    (h : {x : Sˣ | eval₂ (algebraMap R S) x p = eval₂ (algebraMap R S) x q}.Infinite) :
    p = q := by
  have hinj : Function.Injective (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)) :=
    AddMonoidAlgebra.map_injective _ (FaithfulSMul.algebraMap_injective R S)
  exact hinj <| eq_of_infinite_eval₂_id_eq <| by simpa [eval₂_mapRingHom] using h

/-- A Laurent polynomial vanishing at infinitely many units is zero. -/
theorem eq_zero_of_infinite_eval₂_eq_zero [CommSemiring R] [Algebra R S] [FaithfulSMul R S]
    (p : R[T;T⁻¹]) (h : {x : Sˣ | eval₂ (algebraMap R S) x p = 0}.Infinite) : p = 0 :=
  eq_of_infinite_eval₂_eq (S := S) <| by simpa using h

end LaurentPolynomial
