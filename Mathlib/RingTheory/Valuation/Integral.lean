/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationRing

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

lemma isIntegral_iff_v_le_one {x : R} :
    IsIntegral O x ↔ v x ≤ 1 := by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  constructor
  · rintro ⟨f, hm, hf⟩
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [map_eq_zero_iff _ hv.hom_inj, hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v at hf
    simp only [map_neg, map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · simp only [Finset.mem_range, map_mul, map_pow]
      intro _ hi
      exact mul_lt_of_le_one_of_lt (hv.map_le_one _) <| pow_lt_pow_right₀ hf hi
  · intro h
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one h
    exact ⟨Polynomial.X - .C y, by monicity, by simp⟩

theorem mem_of_integral {x : R} (hx : IsIntegral O x) : x ∈ v.integer :=
  hv.isIntegral_iff_v_le_one.mp hx

protected theorem integralClosure : integralClosure O R = ⊥ :=
  bot_unique fun _ hr =>
    let ⟨x, hx⟩ := hv.3 (hv.mem_of_integral hr)
    Algebra.mem_bot.2 ⟨x, hx⟩

end CommRing

section FractionField

variable {K : Type u} {Γ₀ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation K Γ₀} {O : Type w} [CommRing O]
variable [Algebra O K]
variable (hv : Integers v O)

include hv in
theorem isIntegrallyClosed : IsIntegrallyClosed O := by
  have : IsFractionRing O K := hv.isFractionRing
  exact
    (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mp (Valuation.Integers.integralClosure hv)

@[deprecated (since := "2025-09-04")] alias integrallyClosed := isIntegrallyClosed

instance isIntegrallyClosed_integers (v : Valuation K Γ₀) :
    IsIntegrallyClosed v.integer :=
  (Valuation.integer.integers v).isIntegrallyClosed

end FractionField

end Integers

end Valuation
