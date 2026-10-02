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

A Laurent polynomial mapping injectively into an integral domain is determined by its values at
the units of the domain, as soon as there are infinitely many of them: this is the analogue for
`R[T;T⁻¹]` of `Polynomial.eq_zero_of_infinite_isRoot`, and it follows from it by clearing
denominators.

## Main results

* `LaurentPolynomial.eq_zero_of_infinite_eval₂_eq_zero`: a Laurent polynomial vanishing at
  infinitely many units is zero.
* `LaurentPolynomial.eq_of_infinite_eval₂_eq`: two Laurent polynomials agreeing at infinitely
  many units are equal.
-/

@[expose] public section

namespace LaurentPolynomial

variable {R S : Type*} [CommRing S] [IsDomain S]

/-- A Laurent polynomial vanishing at infinitely many units is zero. -/
theorem eq_zero_of_infinite_eval₂_eq_zero [CommSemiring R] {f : R →+* S}
    (hf : Function.Injective f) (p : R[T;T⁻¹])
    (h : {x : Sˣ | eval₂ f x p = 0}.Infinite) : p = 0 := by
  obtain ⟨n, q, hq⟩ := exists_T_pow p
  have hq0 : q = 0 := by
    rw [← Polynomial.map_eq_zero_iff hf]
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injOn_mapsTo Units.val_injective.injOn (fun x hx ↦ ?_) h)
    simpa [Polynomial.IsRoot, Polynomial.eval_map, ← eval₂_toLaurent, hq] using hx
  rw [hq0, map_zero] at hq
  exact (isUnit_T (n : ℤ)).mul_left_eq_zero.mp hq.symm

/-- Two Laurent polynomials agreeing at infinitely many units are equal. -/
theorem eq_of_infinite_eval₂_eq [CommRing R] {f : R →+* S} (hf : Function.Injective f)
    {p q : R[T;T⁻¹]} (h : {x : Sˣ | eval₂ f x p = eval₂ f x q}.Infinite) : p = q :=
  sub_eq_zero.mp <| eq_zero_of_infinite_eval₂_eq_zero hf _ <| by simpa [sub_eq_zero] using h

end LaurentPolynomial
