/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Integers

/-!
# Integral elements over the ring of integers of a valuation

The ring of integers is integrally closed inside the original ring.
-/


universe u v w

namespace Valuation

namespace Integers

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation R Γ₀} {O : Type w} [CommRing O] [Algebra O R] (hv : Integers v O)
include hv

open Polynomial

theorem mem_of_integral {x : R} (hx : IsIntegral O x) : x ∈ v.integer :=
  let ⟨p, hpm, hpx⟩ := hx
  le_of_not_gt fun hvx : 1 < v x => by
    rw [hpm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum, add_eq_zero_iff_eq_neg] at hpx
    replace hpx := congr_arg v hpx; refine ne_of_gt ?_ hpx
    rw [v.map_neg, v.map_pow]
    refine v.map_sum_lt' (zero_lt_one.trans_le (one_le_pow_of_one_le' hvx.le _)) fun i hi => ?_
    rw [eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, v.map_mul, v.map_pow, ←
      one_mul (v x ^ p.natDegree)]
    rcases (hv.2 <| p.coeff i).lt_or_eq with hvpi | hvpi
    · exact mul_lt_mul'' hvpi (pow_lt_pow_right₀ hvx <| Finset.mem_range.1 hi) zero_le' zero_le'
    · rw [hvpi, one_mul, one_mul]; exact pow_lt_pow_right₀ hvx (Finset.mem_range.1 hi)

protected theorem integralClosure : integralClosure O R = ⊥ :=
  bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

end CommRing

section FractionField

variable {K : Type u} {Γ₀ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation K Γ₀} {O : Type w} [CommRing O]
variable [Algebra O K] [IsFractionRing O K]
variable (hv : Integers v O)

include hv in
theorem integrallyClosed : IsIntegrallyClosed O :=
  (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)

end FractionField

end Integers

end Valuation
