/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluation of power series in Hahn Series

We describe a class of ring homomorphisms from formal power series to Hahn series,
given by substitution of the generating variable to an element of strictly positive order.

## Main Definitions
* `HahnSeries.SummableFamily.powerSeriesFamily`: A summable family of Hahn series whose elements
  are non-negative powers of a fixed positive-order Hahn series multiplied by the coefficients of a
  formal power series.
* `PowerSeries.heval`: The `R`-algebra homomorphism from `PowerSeries σ R` to `HahnSeries Γ R` that
  takes `X` to a fixed positive-order Hahn Series and extends to formal infinite sums.

## TODO
* `MvPowerSeries.heval`: An `R`-algebra homomorphism from `MvPowerSeries σ R` to `HahnSeries Γ R`
  (for finite σ) taking each `X i` to a positive order Hahn Series.

-/

open Finset Function

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V]

/-- A summable family given by scalar multiples of powers of a positive order Hahn series.

The scalar multiples are given by the coefficients of a power series. -/
abbrev powerSeriesFamily (x : HahnSeries Γ V) (f : PowerSeries R) : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff n) (powers x)

theorem powerSeriesFamily_of_not_orderTop_pos {x : HahnSeries Γ V} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily 0 f := by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

theorem powerSeriesFamily_of_orderTop_pos {x : HahnSeries Γ V} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : ℕ) :
    powerSeriesFamily x f n = f.coeff n • x ^ n := by
  simp [hx]

theorem powerSeriesFamily_hsum_zero (f : PowerSeries R) :
    (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : HahnSeries Γ V) := by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n ↦ (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

theorem powerSeriesFamily_add {x : HahnSeries Γ V} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

theorem powerSeriesFamily_smul {x : HahnSeries Γ V} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset {x : HahnSeries Γ V} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support ⊆
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : ∃ c ∈ antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g ≠ 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1, powers_of_orderTop_pos h c.2, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← pow_add, hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) ≠ 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

theorem hsum_powerSeriesFamily_mul {x : HahnSeries Γ V} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his ↦ by simpa [h, PowerSeries.coeff_mul, sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm, mul_one]

end PowerSeriesFamily

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : HahnSeries Γ R)

/-- The `R`-algebra homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x` and extending to infinite sums. -/
@[simps]
def heval : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : ℕ) (fun n hn => by simp [hn])]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_toFun, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]

theorem heval_mul {a b : PowerSeries R} :
    heval x (a * b) = heval x a * heval x b :=
  map_mul (heval x) a b

theorem heval_C (r : R) : heval x (C r) = r • 1 := by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [coeff_ne_zero_C hn])]
  by_cases hg : g = 0 <;> simp

theorem heval_X (hx : 0 < x.orderTop) : heval x X = x := by
  rw [X_eq, monomial_eq_mk, heval_apply, powerSeriesFamily, smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum, finsum_eq_single _ 1 (fun n hn ↦ by simp [hn])]
  simp

theorem heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval x u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul, Units.val_inv, map_one]

theorem coeff_heval (f : PowerSeries R) (g : Γ) :
    (heval x f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl

theorem coeff_heval_zero (f : PowerSeries R) :
    (heval x f).coeff 0 = PowerSeries.constantCoeff f := by
  rw [coeff_heval, finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp
  · intro n hn
    simp only [coeff_toFun, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

end PowerSeries
