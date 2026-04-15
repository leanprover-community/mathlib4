/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Valuations associated to DVRs

-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The maximal ideal of a discrete valuation ring. -/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial ↥(valueGroup (valuation K (maximalIdeal A))) := by
    let v := (maximalIdeal A).valuation K
    let π := valuation_exists_uniformizer K (maximalIdeal A) |>.choose
    have hπ : v π = ↑(ofAdd (-1 : ℤ)) :=
      valuation_exists_uniformizer K (maximalIdeal A) |>.choose_spec
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply mem_valueGroup
      simp only [Units.val_mk0, Set.mem_range]
      use π
    · simpa [hπ] using not_eq_of_beq_eq_false rfl
  infer_instance

variable {A K}

open scoped WithZero

theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x ≤ (1 : ℤᵐ⁰)) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_nonZeroDivisors.mp hb).2
    rw [mul_comm (w : A) _, map_mul _ (u : A) _, map_mul _ _ (w : A), div_eq_mul_inv, mul_assoc,
      Valuation.map_mul, Integers.one_of_isUnit' u.isUnit (valuation_le_one _), one_mul,
      mul_inv, ← mul_assoc, Valuation.map_mul, map_mul, map_inv₀, map_inv₀,
      Integers.one_of_isUnit' w.isUnit (valuation_le_one _), inv_one, mul_one, ← div_eq_mul_inv,
      ← map_div₀, ← IsFractionRing.mk'_mk_eq_div hb,
      valuation_of_mk', map_pow, map_pow] at H
    have h_mn : m ≤ n := by
      have v_π_lt_one := (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have v_π_ne_zero : (maximalIdeal A).intValuation π ≠ 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← ofAdd_zero,
        ← zpow_neg, ← zpow_add₀ v_π_ne_zero, ← sub_eq_add_neg] at H
      rwa [← sub_nonneg, ← zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.mpr v_π_ne_zero)
        v_π_lt_one]
    use u * π ^ (n - m) * w.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebraMap A _) ↑w)⁻¹ _, ←
      mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hπ.ne_zero

lemma mker_valuation_eq_isUnitSubmonoid :
    MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).valuation K) =
    (IsUnit.submonoid A).map (algebraMap A K) := by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] at h
    use b, h
  · obtain ⟨x, h, rfl⟩ := h
    simpa [IsDiscreteValuationRing.maximalIdeal] using h

theorem associated_of_valuation_eq (x y : K)
    (h : ((maximalIdeal A).valuation K) x =
    ((maximalIdeal A).valuation K) y) : ∃ u : Aˣ, u • x = y := by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) ∈ MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def, Algebra.smul_def, IsUnit.unit_spec, h.2]
  field_simp

theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR `A` and the valuation subring of a field of fractions
  of `A` endowed with the adic valuation of the maximal ideal. -/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

lemma intValuation_maximalIdeal (x : A) :
    (maximalIdeal A).intValuation x =
      (ENat.recTopCoe 0 (WithZero.coe <| Multiplicative.ofAdd <| Nat.cast · ) (addVal A x))⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, this, WithZero.exp_eq_coe_ofAdd (n : ℤ)]

end IsDiscreteValuationRing

end
