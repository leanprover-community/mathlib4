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

A Laurent polynomial over an integral domain is determined by its values at the units of the ring,
as soon as there are infinitely many of them: this is the analogue for `R[T;T⁻¹]` of
`Polynomial.eq_zero_of_infinite_isRoot`, and it follows from it by clearing denominators.

## Main results

* `LaurentPolynomial.eq_zero_of_infinite_eval₂_eq_zero`: a Laurent polynomial vanishing at
  infinitely many units is zero.
-/

@[expose] public section

namespace LaurentPolynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A Laurent polynomial vanishing at infinitely many units is zero. -/
theorem eq_zero_of_infinite_eval₂_eq_zero (p : R[T;T⁻¹])
    (h : {x : Rˣ | eval₂ (RingHom.id R) x p = 0}.Infinite) : p = 0 := by
  obtain ⟨n, q, hq⟩ := exists_T_pow p
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injOn_mapsTo Units.val_injective.injOn (fun x hx ↦ ?_) h)
    simpa [Polynomial.IsRoot, ← Polynomial.eval₂_id, ← eval₂_toLaurent, hq] using hx
  rw [hq0, map_zero] at hq
  exact (isUnit_T (n : ℤ)).mul_left_eq_zero.mp hq.symm

end LaurentPolynomial
