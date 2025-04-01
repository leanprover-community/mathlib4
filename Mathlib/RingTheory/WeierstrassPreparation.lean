/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
/-!

# Distiguished polynomial

In this section we define the structure `IsDistinguishedAt`
and develope the most basic lemmas about it.

-/

open scoped Polynomial
open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R]

section

/-- Given an ideal `I` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Distinguished at `I`* if `f` is monic and `IsWeaklyEisensteinAt I`. -/
structure Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R) : Prop where
  monic : f.Monic
  else_mem : f.IsWeaklyEisensteinAt I

namespace IsDistinguishedAt

lemma map_eq_X_pow (f : R[X]) {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt|gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.else_mem.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

lemma deg_eq_order_map [Nontrivial R] {I : Ideal R} (f : PowerSeries R)
    (h : R⟦X⟧) (g : R[X]) (distinguish : g.IsDistinguishedAt I) (nmem : ¬ (constantCoeff R) h ∈ I)
    (eq : f = g * h) : g.degree = (f.map (Ideal.Quotient.mk I)).order := by
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero, Eq.comm, PowerSeries.order_eq_nat]
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
    h.map (Ideal.Quotient.mk I) := by
    simp only [← map_eq_X_pow g distinguish, Polynomial.polynomial_map_coe, eq, _root_.map_mul]
  constructor
  · simp [mapf, coeff_X_pow_mul', eq_zero_iff_mem, nmem]
  · intro i hi
    simp [mapf, coeff_X_pow_mul', hi]

end IsDistinguishedAt
