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

/-- A summable family given by scalar multiples of powers of a positive order Hahn series. -/
abbrev powerSeriesFamily : SummableFamily Γ V ℕ :=
  smulFamily (fun n => PowerSeries.coeff R n f) (powers x hx)

@[simp]
theorem powerSeriesFamily_toFun (n : ℕ) :
    powerSeriesFamily hx f n = PowerSeries.coeff R n f • x ^ n :=
  rfl

theorem powerSeriesFamily_add (g : PowerSeries R) :
    powerSeriesFamily hx (f + g) = powerSeriesFamily hx f + powerSeriesFamily hx g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamily_smul (r : R) :
    powerSeriesFamily hx (r • f) = (HahnSeries.single (0 : Γ) r) • (powerSeriesFamily hx f) := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset (hx : 0 < x.orderTop) (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily hx (a * b)).coeff g).support ⊆
    (((powerSeriesFamily hx a).mul (powerSeriesFamily hx b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, smulFamily_toFun, powers_toFun, HahnSeries.smul_coeff,
    mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset,
    coe_image, Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image,
    Function.mem_support, Prod.exists]
  intro n hn
  simp_rw [PowerSeries.coeff_mul, ← ne_eq, sum_smul, mul_smul] at hn
  have he : ∃p ∈ antidiagonal n, ¬((PowerSeries.coeff R p.1) a •
      (PowerSeries.coeff R p.2) b • (x ^ n).coeff g) = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← pow_add, mem_antidiagonal.mp he.choose_spec.1, smul_comm]
  exact he.choose_spec.2

theorem hsum_powerSeriesFamily_mul (hx : 0 < x.orderTop) (a b : PowerSeries R) :
    (powerSeriesFamily hx (a * b)).hsum =
    ((powerSeriesFamily hx a).mul (powerSeriesFamily hx b)).hsum := by
  ext g
  simp only [powerSeriesFamily_toFun, PowerSeries.coeff_mul, Finset.sum_smul, ← Finset.sum_product,
    hsum_coeff_eq_sum, mul_toFun]
  rw [sum_subset (support_powerSeriesFamily_subset hx a b g)]
  · rw [← HahnSeries.sum_coeff, sum_sigma', sum_coeff]
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp_all) ?_ ?_
      (fun _ _ => by simp only [smul_mul_smul_comm, pow_add])).symm
    · intro ij hij
      simp_all only [coeff_support, mul_toFun, powerSeriesFamily_toFun, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, Set.Finite.coe_toFinset,
        Function.mem_support, ne_eq, coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image,
        Prod.exists, mem_coe, mem_antidiagonal, and_true]
      use ij.1, ij.2
    · intro i hi his
      simp_all only [coeff_support, mul_toFun, powerSeriesFamily_toFun, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_sigma, mem_image,
        Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, mem_antidiagonal,
        Set.Finite.coe_toFinset, Set.mem_image, not_exists, not_and]
      have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff R k) b •
          ((PowerSeries.coeff R j) a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        exact his m n
      rw [mul_comm ((PowerSeries.coeff R i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · intro i hi his
    classical
    simp_all only [coeff_support, mul_toFun, powerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_image, Set.Finite.mem_toFinset,
      Function.mem_support, ne_eq, Prod.exists, Decidable.not_not, sum_coeff]
    rwa [PowerSeries.coeff_mul, sum_smul, sum_coeff] at his

end PowerSeriesFamily

end SummableFamily

end HahnSeries
