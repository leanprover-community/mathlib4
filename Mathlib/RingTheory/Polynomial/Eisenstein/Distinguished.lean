/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Order
/-!

# Distinguished polynomial

In this file we define the predicate `Polynomial.IsDistinguishedAt`
and develop the most basic lemmas about it.

-/

open scoped Polynomial
open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R]

/--
Given an ideal `I` of a commutative ring `R`, we say that a polynomial `f : R[X]`
is *Distinguished at `I`* if `f` is monic and `IsWeaklyEisensteinAt I`.
i.e. `f` is of the form `xⁿ + a₁xⁿ⁻¹ + ⋯ + aₙ` with `aᵢ ∈ I` for all `i`.
-/
structure Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R) : Prop
    extends f.IsWeaklyEisensteinAt I where
  monic : f.Monic

namespace IsDistinguishedAt

lemma map_eq_X_pow (f : R[X]) {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt|gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

lemma degree_eq_order_map {I : Ideal R} (f : PowerSeries R)
    (h : R⟦X⟧) (g : R[X]) (distinguish : g.IsDistinguishedAt I) (nmem : ¬ constantCoeff R h ∈ I)
    (eq : f = g * h) : g.degree = (f.map (Ideal.Quotient.mk I)).order := by
  let _ : Nontrivial R := nontrivial_iff.mpr
    ⟨0, constantCoeff R h, ne_of_mem_of_not_mem I.zero_mem nmem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero, Eq.comm, PowerSeries.order_eq_nat]
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
    h.map (Ideal.Quotient.mk I) := by
    simp only [← map_eq_X_pow g distinguish, Polynomial.polynomial_map_coe, eq, _root_.map_mul]
  constructor
  · simp [mapf, coeff_X_pow_mul', eq_zero_iff_mem, nmem]
  · intro i hi
    simp [mapf, coeff_X_pow_mul', hi]

end IsDistinguishedAt
