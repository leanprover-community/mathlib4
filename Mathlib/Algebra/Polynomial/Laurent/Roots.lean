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
over `R` is determined by its evaluations (via `LaurentPolynomial.smeval`) at the units of `S`, as
soon as there are infinitely many of them: this is the analogue for `R[T;T⁻¹]` of
`Polynomial.eq_zero_of_infinite_isRoot`.

## Main results

* `LaurentPolynomial.eq_zero_of_infinite_smeval_eq_zero`: a Laurent polynomial vanishing at
  infinitely many units is zero.
* `LaurentPolynomial.eq_of_infinite_smeval_eq`: two Laurent polynomials agreeing at infinitely
  many units are equal.
-/

@[expose] public section

namespace LaurentPolynomial

variable {R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]

/-- A Laurent polynomial vanishing at infinitely many units is zero. -/
theorem eq_zero_of_infinite_smeval_eq_zero (p : R[T;T⁻¹])
    (h : {x : Sˣ | p.smeval x = 0}.Infinite) : p = 0 := by
  obtain ⟨n, q, hq⟩ := exists_T_pow p
  have hq0 : q = 0 := by
    rw [← Polynomial.map_eq_zero_iff (FaithfulSMul.algebraMap_injective R S)]
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injOn_mapsTo Units.val_injective.injOn (fun x hx ↦ ?_) h)
    rw [Set.mem_ofPred_eq, ← eval₂_eq_smeval] at hx
    simpa [Polynomial.eval_map, hx] using congr(eval₂ (algebraMap R S) x $hq)
  rw [hq0, map_zero] at hq
  exact (isUnit_T (n : ℤ)).mul_left_eq_zero.mp hq.symm

/-- Two Laurent polynomials agreeing at infinitely many units are equal. -/
theorem eq_of_infinite_smeval_eq {p q : R[T;T⁻¹]}
    (h : {x : Sˣ | p.smeval x = q.smeval x}.Infinite) : p = q := by
  have hinj : Function.Injective (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)) :=
    AddMonoidAlgebra.map_injective _ (FaithfulSMul.algebraMap_injective R S)
  refine hinj <| sub_eq_zero.mp <| eq_zero_of_infinite_smeval_eq_zero (S := S) _ ?_
  simpa [← eval₂_eq_smeval, eval₂_mapRingHom, sub_eq_zero] using h

end LaurentPolynomial
