/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.HahnSeries
import Mathlib.RingTheory.Localization.FractionRing

#align_import ring_theory.laurent_series from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Laurent Series

## Main Definitions
* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Provides a coercion `PowerSeries R` into `LaurentSeries R` given by
  `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.

-/


open HahnSeries BigOperators Classical Polynomial

noncomputable section

universe u

/-- A `LaurentSeries` is implemented as a `HahnSeries` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type*) [Zero R] :=
  HahnSeries ℤ R
#align laurent_series LaurentSeries

variable {R : Type u}

namespace LaurentSeries

section Semiring

variable [Semiring R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

/- Porting note: now a syntactic tautology and not needed elsewhere
theorem coe_powerSeries (x : PowerSeries R) :
    (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl -/
#noalign laurent_series.coe_power_series

@[simp]
theorem coeff_coe_powerSeries (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [ofPowerSeries_apply_coeff]
#align laurent_series.coeff_coe_power_series LaurentSeries.coeff_coe_powerSeries

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `powerSeriesPart` has a nonzero
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
theorem powerSeriesPart_zero : powerSeriesPart (0 : LaurentSeries R) = 0 := by
  ext
  simp [(PowerSeries.coeff _ _).map_zero] -- Note: this doesn't get picked up any more
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    simp only [ne_eq]
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
    simp [coeff_order_ne_zero h]
  · rintro rfl
    simp
#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zero

@[simp]
theorem single_order_mul_powerSeriesPart (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x := by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  · rw [Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose! h
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      simp only [Nat.cast_nonneg]
#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPart

theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine' Eq.trans _ (congr rfl x.single_order_mul_powerSeriesPart)
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul]
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
@[simps (config := { rhsMd := .all, simpRhs := true })]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) (LaurentSeries R) where
  map_units' := by
    rintro ⟨_, n, rfl⟩
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      rfl
    · simp only [single_mul_single, mul_one, add_left_neg]
      rfl
    · dsimp; rw [ofPowerSeries_X_pow]
  surj' z := by
    by_cases h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, _⟩
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
    · refine' ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      rw [mul_comm _ z]
      refine' congr rfl _
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact le_of_not_ge h
  exists_of_eq {x y} := by
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    rintro rfl
    exact ⟨1, rfl⟩
#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localization

-- Porting note: this instance is needed
local instance {K : Type u} [Field K] : MonoidWithZero (HahnSeries ℤ K) := inferInstance in
instance {K : Type u} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : PowerSeries K)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type*} [Semiring R] [Ring R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

@[norm_cast] -- Porting note: simp can prove this
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero
#align power_series.coe_zero PowerSeries.coe_zero

@[norm_cast] -- Porting note: simp can prove this
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one
#align power_series.coe_one PowerSeries.coe_one

@[norm_cast] -- Porting note: simp can prove this
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _
#align power_series.coe_add PowerSeries.coe_add

@[norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

@[norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _
#align power_series.coe_neg PowerSeries.coe_neg

@[norm_cast] -- Porting note: simp can prove this
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
#align power_series.coe_mul PowerSeries.coe_mul

theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i =
      if i < 0 then 0 else PowerSeries.coeff R i.natAbs f := by
  cases i
  · rw [Int.ofNat_eq_coe, coeff_coe_powerSeries, if_neg (Int.coe_nat_nonneg _).not_lt,
      Int.natAbs_ofNat]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne.def, toPowerSeries_symm_apply_coeff, mem_support, imp_true_iff,
      not_false_iff]
#align power_series.coeff_coe PowerSeries.coeff_coe

-- Porting note: simp can prove this, and removed norm_cast attribute
theorem coe_C (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _
set_option linter.uppercaseLean3 false in
#align power_series.coe_C PowerSeries.coe_C

-- @[simp] -- Porting note: simp can prove this
theorem coe_X : ((X : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  ofPowerSeries_X
set_option linter.uppercaseLean3 false in
#align power_series.coe_X PowerSeries.coe_X

@[simp, norm_cast]
theorem coe_smul {S : Type*} [Semiring S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • (ofPowerSeries ℤ S x) := by
  ext
  simp [coeff_coe, coeff_smul, smul_ite]
#align power_series.coe_smul PowerSeries.coe_smul

-- Porting note: RingHom.map_bit0 and RingHom.map_bit1 no longer exist
#noalign power_series.coe_bit0
#noalign power_series.coe_bit1

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries
