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

namespace Polynomial.IsDistinguishedAt

lemma mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
    (f * f').IsDistinguishedAt I :=
  ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

lemma map_eq_X_pow {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt|gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

@[deprecated (since := "2025-04-27")]
alias _root_.IsDistinguishedAt.map_eq_X_pow := map_eq_X_pow

section degree_eq_order_map

variable {I : Ideal R} (f h : R⟦X⟧) {g : R[X]}

lemma map_ne_zero_of_eq_mul (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    f.map (Ideal.Quotient.mk I) ≠ 0 := fun H ↦ by
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  apply_fun PowerSeries.coeff g.natDegree at H
  simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem] at H

lemma degree_eq_coe_lift_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.degree = (f.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (distinguish.map_ne_zero_of_eq_mul f h notMem eq)) := by
  have : Nontrivial R := _root_.nontrivial_iff.mpr
    ⟨0, PowerSeries.constantCoeff h, ne_of_mem_of_not_mem I.zero_mem notMem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero, Nat.cast_inj, ← ENat.coe_inj,
    ENat.coe_lift, Eq.comm, PowerSeries.order_eq_nat]
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  constructor
  · simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem]
  · intro i hi
    simp [mapf, PowerSeries.coeff_X_pow_mul', hi]

@[deprecated (since := "2025-04-27")]
alias _root_.IsDistinguishedAt.degree_eq_order_map := degree_eq_coe_lift_order_map

@[deprecated (since := "2025-05-19")]
alias degree_eq_order_map := degree_eq_coe_lift_order_map

lemma coe_natDegree_eq_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.natDegree = (f.map (Ideal.Quotient.mk I)).order := by
  rw [natDegree, distinguish.degree_eq_coe_lift_order_map f h notMem eq]
  exact ENat.coe_lift _ <| order_finite_iff_ne_zero.2 <|
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

end degree_eq_order_map

end Polynomial.IsDistinguishedAt
