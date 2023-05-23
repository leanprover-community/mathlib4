/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.laurent_series
! leanprover-community/mathlib commit 831c494092374cfe9f50591ed0ac81a25efc5b86
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.HahnSeries
import Mathbin.RingTheory.Localization.FractionRing

/-!
# Laurent Series

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/


open HahnSeries

open BigOperators Classical Polynomial

noncomputable section

universe u

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type _) [Zero R] :=
  HahnSeries ℤ R
#align laurent_series LaurentSeries

variable {R : Type u}

namespace LaurentSeries

section Semiring

variable [Semiring R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

theorem coe_powerSeries (x : PowerSeries R) :
    (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl
#align laurent_series.coe_power_series LaurentSeries.coe_powerSeries

@[simp]
theorem coeff_coe_powerSeries (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [coe_power_series, of_power_series_apply_coeff]
#align laurent_series.coeff_coe_power_series LaurentSeries.coeff_coe_powerSeries

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def powerSeriesPart (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)
#align laurent_series.power_series_part LaurentSeries.powerSeriesPart

@[simp]
theorem powerSeriesPart_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _
#align laurent_series.power_series_part_coeff LaurentSeries.powerSeriesPart_coeff

@[simp]
theorem powerSeriesPart_zero : powerSeriesPart (0 : LaurentSeries R) = 0 :=
  by
  ext
  simp
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 :=
  by
  constructor
  · contrapose!
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
    simp [coeff_order_ne_zero h]
  · rintro rfl
    simp
#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zero

@[simp]
theorem single_order_mul_powerSeriesPart (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x :=
  by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  ·
    rw [Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series,
      power_series_part_coeff, ← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right]
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose! h
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      exact Int.zero_le_ofNat _
#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPart

theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x :=
  by
  refine' Eq.trans _ (congr rfl x.single_order_mul_power_series_part)
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul,
    coe_power_series]
#align laurent_series.of_power_series_power_series_part LaurentSeries.ofPowerSeries_powerSeriesPart

end Semiring

instance [CommSemiring R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl
#align laurent_series.coe_algebra_map LaurentSeries.coe_algebraMap

/-- The localization map from power series to Laurent series. -/
@[simps]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) (LaurentSeries R)
    where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      rfl
    · simp only [single_mul_single, mul_one, add_left_neg]
      rfl
    · simp
  surj := by
    intro z
    by_cases h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.X ^ Int.natAbs z.order * power_series_part z, 1⟩, _⟩
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebra_map, of_power_series_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part]
    · refine' ⟨⟨power_series_part z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [coe_algebra_map, of_power_series_power_series_part]
      rw [mul_comm _ z]
      refine' congr rfl _
      rw [Subtype.coe_mk, of_power_series_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact le_of_not_ge h
  eq_iff_exists := by
    intro x y
    rw [coe_algebra_map, of_power_series_injective.eq_iff]
    constructor
    · rintro rfl
      exact ⟨1, rfl⟩
    · rintro ⟨⟨_, n, rfl⟩, hc⟩
      rw [← sub_eq_zero, ← mul_sub, PowerSeries.ext_iff] at hc
      rw [← sub_eq_zero, PowerSeries.ext_iff]
      intro m
      have h := hc (m + n)
      rwa [LinearMap.map_zero, Subtype.coe_mk, PowerSeries.X_pow_eq, PowerSeries.monomial,
        add_comm m, PowerSeries.coeff, Finsupp.single_add, MvPowerSeries.coeff_add_monomial_mul,
        one_mul] at h
#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localization

instance {K : Type u} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : PowerSeries K)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun f hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type _} [Semiring R] [Ring R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

@[simp, norm_cast]
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero
#align power_series.coe_zero PowerSeries.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one
#align power_series.coe_one PowerSeries.coe_one

@[simp, norm_cast]
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _
#align power_series.coe_add PowerSeries.coe_add

@[simp, norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

@[simp, norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _
#align power_series.coe_neg PowerSeries.coe_neg

@[simp, norm_cast]
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
#align power_series.coe_mul PowerSeries.coe_mul

theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i =
      if i < 0 then 0 else PowerSeries.coeff R i.natAbs f :=
  by
  cases i
  ·
    rw [Int.natAbs_ofNat_core, Int.ofNat_eq_coe, coeff_coe_power_series,
      if_neg (Int.coe_nat_nonneg _).not_lt]
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_image_support,
      if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne.def, to_power_series_symm_apply_coeff, mem_support, Int.coe_nat_eq, imp_true_iff,
      not_false_iff]
#align power_series.coeff_coe PowerSeries.coeff_coe

@[simp, norm_cast]
theorem coe_c (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _
#align power_series.coe_C PowerSeries.coe_c

@[simp]
theorem coe_x : ((X : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  ofPowerSeries_X
#align power_series.coe_X PowerSeries.coe_x

@[simp, norm_cast]
theorem coe_smul {S : Type _} [Semiring S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • x :=
  by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]
#align power_series.coe_smul PowerSeries.coe_smul

@[simp, norm_cast]
theorem coe_bit0 : ((bit0 f : PowerSeries R) : LaurentSeries R) = bit0 f :=
  (ofPowerSeries ℤ R).map_bit0 _
#align power_series.coe_bit0 PowerSeries.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 : ((bit1 f : PowerSeries R) : LaurentSeries R) = bit1 f :=
  (ofPowerSeries ℤ R).map_bit1 _
#align power_series.coe_bit1 PowerSeries.coe_bit1

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = f ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries

