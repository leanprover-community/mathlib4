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
  -- 🎉 no goals
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
  -- ⊢ ↑(PowerSeries.coeff R n✝) (powerSeriesPart 0) = ↑(PowerSeries.coeff R n✝) 0
  simp
  -- 🎉 no goals
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 := by
  constructor
  -- ⊢ powerSeriesPart x = 0 → x = 0
  · contrapose!
    -- ⊢ x ≠ 0 → powerSeriesPart x ≠ 0
    simp only [ne_eq]
    -- ⊢ ¬x = 0 → ¬powerSeriesPart x = 0
    intro h
    -- ⊢ ¬powerSeriesPart x = 0
    rw [PowerSeries.ext_iff, not_forall]
    -- ⊢ ∃ x_1, ¬↑(PowerSeries.coeff R x_1) (powerSeriesPart x) = ↑(PowerSeries.coeff …
    refine' ⟨0, _⟩
    -- ⊢ ¬↑(PowerSeries.coeff R 0) (powerSeriesPart x) = ↑(PowerSeries.coeff R 0) 0
    simp [coeff_order_ne_zero h]
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ powerSeriesPart 0 = 0
    simp
    -- 🎉 no goals
#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zero

@[simp]
theorem single_order_mul_powerSeriesPart (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x := by
  ext n
  -- ⊢ HahnSeries.coeff (↑(single (order x)) 1 * ↑(ofPowerSeries ℤ R) (powerSeriesP …
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul]
  -- ⊢ HahnSeries.coeff (↑(ofPowerSeries ℤ R) (powerSeriesPart x)) (n - order x) =  …
  by_cases h : x.order ≤ n
  -- ⊢ HahnSeries.coeff (↑(ofPowerSeries ℤ R) (powerSeriesPart x)) (n - order x) =  …
  · rw [Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h), coeff_coe_powerSeries,
      powerSeriesPart_coeff, ← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right]
  · rw [ofPowerSeries_apply, embDomain_notin_range]
    -- ⊢ 0 = HahnSeries.coeff x n
    · contrapose! h
      -- ⊢ order x ≤ n
      exact order_le_of_coeff_ne_zero h.symm
      -- 🎉 no goals
    · contrapose! h
      -- ⊢ order x ≤ n
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      -- ⊢ order x ≤ n
      obtain ⟨m, hm⟩ := h
      -- ⊢ order x ≤ n
      rw [← sub_nonneg, ← hm]
      -- ⊢ 0 ≤ ↑m
      simp only [Nat.cast_nonneg]
      -- 🎉 no goals
#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPart

theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x := by
  refine' Eq.trans _ (congr rfl x.single_order_mul_powerSeriesPart)
  -- ⊢ ↑(ofPowerSeries ℤ R) (powerSeriesPart x) = ↑(single (-order x)) 1 * (↑(singl …
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul]
  -- 🎉 no goals
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
    -- ⊢ IsUnit (↑(algebraMap (PowerSeries R) (LaurentSeries R)) ↑{ val := (fun x x_1 …
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      -- ⊢ ↑(single 0) 1 = 1
      rfl
      -- 🎉 no goals
    · simp only [single_mul_single, mul_one, add_left_neg]
      -- ⊢ ↑(single 0) 1 = 1
      rfl
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  surj' := by
    intro z
    -- ⊢ ∃ x, z * ↑(algebraMap (PowerSeries R) (LaurentSeries R)) ↑x.snd = ↑(algebraM …
    by_cases h : 0 ≤ z.order
    -- ⊢ ∃ x, z * ↑(algebraMap (PowerSeries R) (LaurentSeries R)) ↑x.snd = ↑(algebraM …
    · refine' ⟨⟨PowerSeries.X ^ Int.natAbs z.order * powerSeriesPart z, 1⟩, _⟩
      -- ⊢ z * ↑(algebraMap (PowerSeries R) (LaurentSeries R)) ↑(PowerSeries.X ^ Int.na …
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebraMap, ofPowerSeries_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, single_order_mul_powerSeriesPart]
      -- 🎉 no goals
    · refine' ⟨⟨powerSeriesPart z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      -- ⊢ z * ↑(algebraMap (PowerSeries R) (LaurentSeries R)) ↑(powerSeriesPart z, { v …
      simp only [coe_algebraMap, ofPowerSeries_powerSeriesPart]
      -- ⊢ z * ↑(ofPowerSeries ℤ R) (PowerSeries.X ^ Int.natAbs (order z)) = ↑(single ( …
      rw [mul_comm _ z]
      -- ⊢ z * ↑(ofPowerSeries ℤ R) (PowerSeries.X ^ Int.natAbs (order z)) = z * ↑(sing …
      refine' congr rfl _
      -- ⊢ ↑(ofPowerSeries ℤ R) (PowerSeries.X ^ Int.natAbs (order z)) = ↑(single (-ord …
      rw [ofPowerSeries_X_pow, Int.ofNat_natAbs_of_nonpos]
      -- ⊢ order z ≤ 0
      exact le_of_not_ge h
      -- 🎉 no goals
  eq_iff_exists' := by
    intro x y
    -- ⊢ ↑(algebraMap (PowerSeries R) (LaurentSeries R)) x = ↑(algebraMap (PowerSerie …
    rw [coe_algebraMap, ofPowerSeries_injective.eq_iff]
    -- ⊢ x = y ↔ ∃ c, ↑c * x = ↑c * y
    constructor
    -- ⊢ x = y → ∃ c, ↑c * x = ↑c * y
    · rintro rfl
      -- ⊢ ∃ c, ↑c * x = ↑c * x
      exact ⟨1, rfl⟩
      -- 🎉 no goals
    · rintro ⟨⟨_, n, rfl⟩, hc⟩
      -- ⊢ x = y
      rw [← sub_eq_zero, ← mul_sub, PowerSeries.ext_iff] at hc
      -- ⊢ x = y
      rw [← sub_eq_zero, PowerSeries.ext_iff]
      -- ⊢ ∀ (n : ℕ), ↑(PowerSeries.coeff R n) (x - y) = ↑(PowerSeries.coeff R n) 0
      intro m
      -- ⊢ ↑(PowerSeries.coeff R m) (x - y) = ↑(PowerSeries.coeff R m) 0
      have h := hc (m + n)
      -- ⊢ ↑(PowerSeries.coeff R m) (x - y) = ↑(PowerSeries.coeff R m) 0
      simp only at h
      -- ⊢ ↑(PowerSeries.coeff R m) (x - y) = ↑(PowerSeries.coeff R m) 0
      rwa [LinearMap.map_zero, PowerSeries.X_pow_eq, PowerSeries.monomial,
        add_comm m, PowerSeries.coeff, Finsupp.single_add, MvPowerSeries.coeff_add_monomial_mul,
        one_mul] at h
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

@[simp, norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

@[simp, norm_cast]
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
  -- ⊢ HahnSeries.coeff (↑(ofPowerSeries ℤ R) f) (Int.ofNat a✝) = if Int.ofNat a✝ < …
  · rw [Int.ofNat_eq_coe, coeff_coe_powerSeries, if_neg (Int.coe_nat_nonneg _).not_lt,
      Int.natAbs_ofNat]
  · rw [ofPowerSeries_apply, embDomain_notin_image_support, if_pos (Int.negSucc_lt_zero _)]
    -- ⊢ ¬Int.negSucc a✝ ∈ ↑{ toEmbedding := { toFun := Nat.cast, inj' := (_ : Functi …
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
  -- ⊢ HahnSeries.coeff (↑(ofPowerSeries ℤ S) (r • x)) x✝ = HahnSeries.coeff (r • ↑ …
  simp [coeff_coe, coeff_smul, smul_ite]
  -- 🎉 no goals
#align power_series.coe_smul PowerSeries.coe_smul

-- Porting note: RingHom.map_bit0 and RingHom.map_bit1 no longer exist
#noalign power_series.coe_bit0
#noalign power_series.coe_bit1

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = (ofPowerSeries ℤ R f) ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries
