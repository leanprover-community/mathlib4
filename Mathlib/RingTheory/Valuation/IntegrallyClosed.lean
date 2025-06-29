/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Valuation subring is integrally closed

-/

namespace Valuation

variable {R F Γ₀ O : Type*} [CommRing R] [Field F]
  [LinearOrderedCommGroupWithZero Γ₀] [CommRing O] [Algebra O R] [Algebra O F]

lemma Integers.v_le_one_of_isIntegral {v : Valuation R Γ₀} (hv : v.Integers O)
    {x : R} (hx : IsIntegral O x) : v x ≤ 1 := by
  nontriviality R
  have : Nontrivial O := hv.nontrivial_iff.mpr inferInstance
  obtain ⟨f, hm, hf⟩ := hx
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    simp [map_eq_zero_iff _ hv.hom_inj, hm.C_ne_zero] at hf
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

lemma Integers.isIntegrallyClosed {v : Valuation F Γ₀} (hv : v.Integers O) :
    IsIntegrallyClosed O := by
  have : IsFractionRing O F := hv.isFractionRing
  rw [isIntegrallyClosed_iff F]
  intro _ hx
  exact hv.exists_of_le_one (hv.v_le_one_of_isIntegral hx)

instance isIntegrallyClosed_integers (v : Valuation F Γ₀) :
    IsIntegrallyClosed v.integer :=
  (Valuation.integer.integers v).isIntegrallyClosed

end Valuation
