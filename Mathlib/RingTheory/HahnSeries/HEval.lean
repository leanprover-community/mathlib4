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

## TODO
 * `PowerSeries.heval`: An `R`-algebra homomorphism from `PowerSeries R` to `HahnSeries Γ R` taking
   `X` to a positive order Hahn Series.

-/

open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V] {x : HahnSeries Γ V} (hx : 0 < x.orderTop) (f : PowerSeries R)

/-- A summable family given by scalar multiples of powers of a positive order Hahn series.

The scalar multiples are given by the coefficients of a power series. -/
abbrev powerSeriesFamily : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff R n) (powers x hx)

@[simp]
theorem powerSeriesFamily_apply (n : ℕ) :
    powerSeriesFamily hx f n = f.coeff R n • x ^ n :=
  rfl

theorem powerSeriesFamily_add (g : PowerSeries R) :
    powerSeriesFamily hx (f + g) = powerSeriesFamily hx f + powerSeriesFamily hx g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamily_smul (r : R) :
    powerSeriesFamily hx (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily hx f := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset (hx : 0 < x.orderTop) (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily hx (a * b)).coeff g).support ⊆
    (((powerSeriesFamily hx a).mul (powerSeriesFamily hx b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp only [coeff_support, smulFamily_toFun, HahnSeries.coeff_smul, Set.Finite.toFinset_subset,
    coe_image, support_subset_iff, Set.mem_image, Prod.exists]
  intro n hn
  simp_rw [PowerSeries.coeff_mul, sum_smul, mul_smul] at hn
  have he := exists_ne_zero_of_sum_ne_zero hn
  simp only [powers_toFun, mem_antidiagonal] at he
  use he.choose.1, he.choose.2
  refine ⟨?_, he.choose_spec.1⟩
  simp only [mul_toFun, smulFamily_toFun, powers_toFun, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, HahnSeries.coeff_smul, Set.Finite.coe_toFinset, ne_eq, Prod.mk.eta,
    Function.mem_support]
  rw [← pow_add, smul_comm, he.choose_spec.1]
  exact he.choose_spec.2

theorem hsum_powerSeriesFamily_mul (hx : 0 < x.orderTop) (a b : PowerSeries R) :
    (powerSeriesFamily hx (a * b)).hsum =
    ((powerSeriesFamily hx a).mul (powerSeriesFamily hx b)).hsum := by
  ext g
  simp only [powerSeriesFamily_apply, PowerSeries.coeff_mul, Finset.sum_smul, ← Finset.sum_product,
    coeff_hsum_eq_sum, mul_toFun]
  rw [sum_subset (support_powerSeriesFamily_subset hx a b g)]
  · rw [← coeff_sum, sum_sigma', coeff_sum]
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp_all) ?_ ?_
      (fun _ _ => by simp only [smul_mul_smul_comm, pow_add])).symm
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
        simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, Set.Finite.coe_toFinset, Set.mem_image,
          Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff R i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · intro i hi his
    simpa [PowerSeries.coeff_mul, sum_smul] using his

end PowerSeriesFamily

end SummableFamily

end HahnSeries
