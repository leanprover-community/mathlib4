/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A summable family given by a power series

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

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V]

/-- A summable family given by scalar multiples of powers of a positive order Hahn series.

The scalar multiples are given by the coefficients of a power series. -/
abbrev powerSeriesFamily (x : HahnSeries Γ V) (f : PowerSeries R) : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff R n) (powers x)

theorem powerSeriesFamily_of_not_orderTop_pos {x : HahnSeries Γ V} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = 0 := by
  ext
  simp [powers_of_not_orderTop_pos hx]

theorem powerSeriesFamily_of_orderTop_pos {x : HahnSeries Γ V} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : ℕ) :
    powerSeriesFamily x f n = f.coeff R n • x ^ n := by
  simp [hx]

theorem powerSeriesFamily_add {x : HahnSeries Γ V} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamily_smul {x : HahnSeries Γ V} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset {x : HahnSeries Γ V} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support ⊆
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop; swap; · simp [h]
  simp only [coeff_support, smulFamily_toFun, powers_of_orderTop_pos h, HahnSeries.coeff_smul,
    mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset, coe_image,
    Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image, Function.mem_support,
    Prod.exists]
  intro n hn
  simp_rw [PowerSeries.coeff_mul, sum_smul, mul_smul] at hn
  have he := exists_ne_zero_of_sum_ne_zero hn
  simp only [powers_of_orderTop_pos h, mem_antidiagonal] at he
  use he.choose.1, he.choose.2
  refine ⟨?_, he.choose_spec.1⟩
  simp only [mul_toFun, smulFamily_toFun, powers_of_orderTop_pos h, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, HahnSeries.coeff_smul, Set.Finite.coe_toFinset, ne_eq, Prod.mk.eta,
    Function.mem_support]
  rw [← pow_add, smul_comm, he.choose_spec.1]
  exact he.choose_spec.2

theorem hsum_powerSeriesFamily_mul {x : HahnSeries Γ V} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop; swap; · simp [hsum_mul, powerSeriesFamily_of_not_orderTop_pos h]
  simp only [not_not] at h
  ext g
  simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos, HahnSeries.coeff_smul,
    mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [sum_subset (support_powerSeriesFamily_subset a b g)
    (fun i hi his ↦ by simpa [h, PowerSeries.coeff_mul, sum_smul] using his)]
  simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
  rw [sum_sigma']
  refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp_all) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
  · intro ij hij
    simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
      mem_antidiagonal, and_true]
    use ij.1, ij.2
    simp_all
  · intro i hi his
    have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff R k) b •
        (PowerSeries.coeff R j a • (x ^ j * x ^ k).coeff g) = 0 := by
      intro m n
      contrapose!
      simp only [coeff_support, mul_toFun, smulFamily_toFun, powers_of_orderTop_pos h,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, HahnSeries.coeff_smul,
        Set.Finite.coe_toFinset, Set.mem_image, Function.mem_support, ne_eq, Prod.exists,
        not_exists, not_and] at his
      exact his m n
    simp only [mem_sigma, mem_antidiagonal] at hi
    rw [mul_comm ((PowerSeries.coeff R i.snd.1) a), ← hi.2, mul_smul, pow_add]
    exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)

end PowerSeriesFamily

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

/-- The `R`-algebra homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x` and extending to infinite sums. -/
@[simps]
def heval : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_of_orderTop_pos hx, ite_smul, one_smul,
      zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : ℕ) (fun n hn => by simp_all)]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, powers_of_orderTop_pos, smul_ite, zero_smul,
      smul_zero, ite_self, coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_of_orderTop_pos, hx, ↓reduceIte,
      ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp_all]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]

theorem heval_mul {a b : PowerSeries R} :
    heval hx (a * b) = (heval hx a) * heval hx b :=
  map_mul (heval hx) a b

theorem heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval hx u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval hx u.inv
  rw [← heval_mul, Units.val_inv, map_one]

theorem coeff_heval (f : PowerSeries R) (g : Γ) :
    (heval hx f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl

theorem coeff_heval_zero (f : PowerSeries R) :
    (heval hx f).coeff 0 = PowerSeries.constantCoeff R f := by
  rw [coeff_heval, finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp_all
  · intro n hn
    simp_all only [ne_eq, coeff_toFun, smulFamily_toFun, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, smul_eq_mul]
    exact mul_eq_zero_of_right ((PowerSeries.coeff R n) f) (coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr hx) orderTop_nsmul_le_orderTop_pow))

end PowerSeries
