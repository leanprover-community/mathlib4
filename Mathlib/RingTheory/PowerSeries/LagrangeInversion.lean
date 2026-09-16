/-
Copyright (c) 2026 manman4. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: manman4
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal Lagrange inversion

This file proves the coefficient form of the one-variable Lagrange inversion theorem for formal
power series. No analytic convergence is involved.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

open Polynomial
open scoped PowerSeries LaurentSeries

variable {K : Type*} [Field K]

private def tail (B : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) B

private def residue (F : K⸨X⸩) : K :=
  F.coeff (-1)

private theorem residue_add (F G : K⸨X⸩) :
    residue (F + G) = residue F + residue G := by
  simp [residue, HahnSeries.coeff_add']

private theorem residue_sub (F G : K⸨X⸩) :
    residue (F - G) = residue F - residue G := by
  simp [residue, HahnSeries.coeff_sub]

private theorem residue_algebraMap_mul (a : K) (F : K⸨X⸩) :
    residue (algebraMap K K⸨X⸩ a * F) = a * residue F := by
  unfold residue
  rw [LaurentSeries.algebraMap_apply]
  exact HahnSeries.coeff_single_zero_mul

private theorem tail_constantCoeff (B : K⟦X⟧) :
    PowerSeries.constantCoeff (tail B) = PowerSeries.coeff 1 B := by
  simp [tail]

private theorem eq_X_mul_tail {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0) :
    B = PowerSeries.X * tail B := by
  rw [PowerSeries.eq_X_mul_shift_add_const B, hB0]
  simp [tail]

private theorem residue_single_neg_succ_mul_coe (q : ℕ) (F : K⟦X⟧) :
    residue
        (HahnSeries.single (-(q + 1 : ℤ)) 1 * (F : K⸨X⸩)) =
      PowerSeries.coeff q F := by
  simp [residue, HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]

private theorem coe_inv_of_constantCoeff_ne_zero (F : K⟦X⟧)
    (hF : PowerSeries.constantCoeff F ≠ 0) :
    ((F⁻¹ : K⟦X⟧) : K⸨X⸩) = ((F : K⸨X⸩)⁻¹) := by
  apply eq_inv_of_mul_eq_one_left
  rw [← PowerSeries.coe_mul, PowerSeries.inv_mul_cancel F hF]
  exact PowerSeries.coe_one

private theorem derivative_inv_pow (F : K⟦X⟧) (q : ℕ) :
    (d⁄dX) (F⁻¹ ^ q) =
      PowerSeries.C (-(q : K)) *
        (F⁻¹ ^ (q + 1) * (d⁄dX) F) := by
  cases q with
  | zero => simp
  | succ q =>
      rw [Derivation.leibniz_pow, PowerSeries.derivative_inv']
      simp only [Nat.succ_sub_one, smul_eq_mul]
      push_cast
      rw [pow_succ (F⁻¹) (q + 1), pow_succ (F⁻¹) q]
      rw [PowerSeries.C_eq_algebraMap]
      push_cast
      ring

private theorem coeff_inverse_power_log_derivative [CharZero K] (F : K⟦X⟧)
    (hF : PowerSeries.constantCoeff F = 1) (q : ℕ) :
    PowerSeries.coeff q
        (F⁻¹ ^ (q + 1) * (F + PowerSeries.X * (d⁄dX) F)) =
      if q = 0 then 1 else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
  · have hqne : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have hunit : F⁻¹ * F = (1 : K⟦X⟧) :=
      PowerSeries.inv_mul_cancel F (by simp [hF])
    have hfirst : F⁻¹ ^ (q + 1) * F = F⁻¹ ^ q := by
      rw [pow_succ]
      calc
        F⁻¹ ^ q * F⁻¹ * F = F⁻¹ ^ q * (F⁻¹ * F) := by ring
        _ = F⁻¹ ^ q := by rw [hunit, mul_one]
    have hderiv := congrArg (PowerSeries.coeff (q - 1))
      (derivative_inv_pow F q)
    rw [PowerSeries.coeff_derivative] at hderiv
    have hqsplit : q - 1 + 1 = q := by omega
    rw [hqsplit] at hderiv
    have hqcast : ((q - 1 : ℕ) : K) + 1 = q := by
      exact_mod_cast hqsplit
    rw [hqcast] at hderiv
    rw [PowerSeries.coeff_C_mul] at hderiv
    have hcoeff :
        (q : K) * PowerSeries.coeff q (F⁻¹ ^ q) =
          -(q : K) *
            PowerSeries.coeff (q - 1)
              (F⁻¹ ^ (q + 1) * (d⁄dX) F) := by
      simpa [mul_comm] using hderiv
    rw [ite_eq_right hq]
    rw [mul_add, hfirst, ← mul_assoc]
    rw [map_add]
    have hsecond :
        PowerSeries.coeff q
            (F⁻¹ ^ (q + 1) * PowerSeries.X * (d⁄dX) F) =
          PowerSeries.coeff (q - 1)
            (F⁻¹ ^ (q + 1) * (d⁄dX) F) := by
      calc
        _ = PowerSeries.coeff q
            (PowerSeries.X * (F⁻¹ ^ (q + 1) * (d⁄dX) F)) := by
              congr 1
              ring
        _ = _ := by
          have hs := PowerSeries.coeff_succ_X_mul (q - 1)
            (F⁻¹ ^ (q + 1) * (d⁄dX) F)
          rw [hqsplit] at hs
          exact hs
    rw [hsecond]
    apply mul_left_cancel₀ hqne
    rw [mul_zero, mul_add, hcoeff]
    ring

private theorem derivative_eq_tail_add {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0) :
    (d⁄dX) B = tail B + PowerSeries.X * (d⁄dX) (tail B) := by
  calc
    (d⁄dX) B = (d⁄dX) (PowerSeries.X * tail B) := by
      rw [← eq_X_mul_tail hB0]
    _ = _ := by
      rw [Derivation.leibniz]
      simp only [PowerSeries.derivative_X, smul_eq_mul]
      ring

private theorem coe_zpow_negSucc_eq {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB1 : PowerSeries.coeff 1 B = 1) (q : ℕ) :
    ((B : K⸨X⸩) ^ (Int.negSucc q)) =
      HahnSeries.single (-(q + 1 : ℤ)) 1 *
        (((tail B)⁻¹ ^ (q + 1) : K⟦X⟧) : K⸨X⸩) := by
  have htail : PowerSeries.constantCoeff (tail B) = 1 := by
    rw [tail_constantCoeff, hB1]
  have hfactor :
      (B : K⸨X⸩) =
        HahnSeries.single (1 : ℤ) 1 * ((tail B : K⟦X⟧) : K⸨X⸩) := by
    calc
      (B : K⸨X⸩) = ((PowerSeries.X * tail B : K⟦X⟧) : K⸨X⸩) := by
        rw [← eq_X_mul_tail hB0]
      _ = _ := by rw [PowerSeries.coe_mul, PowerSeries.coe_X]
  have hinv := coe_inv_of_constantCoeff_ne_zero (tail B) (by simp [htail])
  rw [zpow_negSucc, hfactor, mul_pow, mul_inv_rev]
  rw [← inv_pow, ← inv_pow, ← hinv, ← PowerSeries.coe_pow]
  rw [HahnSeries.inv_single, HahnSeries.single_pow]
  norm_num
  ring

private theorem residue_zpow_mul_derivative [CharZero K] {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB1 : PowerSeries.coeff 1 B = 1) (z : ℤ) :
    residue
        (((B : K⸨X⸩) ^ z) *
          (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
      if z = -1 then 1 else 0 := by
  cases z with
  | ofNat k =>
      rw [ite_eq_right (by simp)]
      change residue
        (((B : K⸨X⸩) ^ (k : ℕ)) *
          (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) = 0
      have hprod :
          (B : K⸨X⸩) ^ k * (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
            (((B ^ k) * (d⁄dX) B : K⟦X⟧) : K⸨X⸩) := by
        rw [PowerSeries.coe_mul, PowerSeries.coe_pow]
      calc
        residue
            ((B : K⸨X⸩) ^ k *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
            residue ((((B ^ k) * (d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by
              exact congrArg residue hprod
        _ = 0 := by
          unfold residue
          rw [PowerSeries.coeff_coe]
          norm_num
  | negSucc q =>
      rw [coe_zpow_negSucc_eq hB0 hB1 q, derivative_eq_tail_add hB0]
      rw [mul_assoc, ← PowerSeries.coe_mul]
      rw [residue_single_neg_succ_mul_coe]
      rw [coeff_inverse_power_log_derivative (tail B)
        (by rw [tail_constantCoeff, hB1])]
      simp [Int.negSucc_eq]

private theorem residue_shifted_aeval_mul_derivative [CharZero K] {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0)
    (hB1 : PowerSeries.coeff 1 B = 1) (p : K[X]) (n : ℕ) :
    residue
        (((B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ))) *
          Polynomial.aeval (B : K⸨X⸩) p *
          (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
      p.coeff n := by
  have hBne : (B : K⸨X⸩) ≠ 0 := by
    intro h
    have hzero : B = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      simpa using h
    rw [hzero] at hB1
    norm_num at hB1
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      have hsplit :
          (B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
                (Polynomial.aeval (B : K⸨X⸩) p +
                  Polynomial.aeval (B : K⸨X⸩) q) *
                (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
            ((B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
                Polynomial.aeval (B : K⸨X⸩) p *
                (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) +
              ((B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
                Polynomial.aeval (B : K⸨X⸩) q *
                (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by ring
      rw [hsplit]
      rw [residue_add, hp, hq]
      simp
  | monomial k a =>
      rw [Polynomial.aeval_def, Polynomial.eval₂_monomial]
      have hzpow :
          (B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
              (B : K⸨X⸩) ^ k =
            (B : K⸨X⸩) ^ ((k : ℤ) - (n + 1 : ℤ)) := by
        rw [← zpow_natCast]
        rw [← zpow_add₀ hBne]
        congr 1
      have hreorder :
          ((B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
                (algebraMap K K⸨X⸩ a * (B : K⸨X⸩) ^ k)) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
            algebraMap K K⸨X⸩ a *
              (((B : K⸨X⸩) ^ (-((n + 1 : ℕ) : ℤ)) *
                  (B : K⸨X⸩) ^ k) *
                (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by ring
      rw [hreorder, hzpow, residue_algebraMap_mul]
      rw [residue_zpow_mul_derivative hB0 hB1]
      by_cases hkn : k = n
      · subst k
        simp
      · have hexp : (k : ℤ) - (n + 1 : ℤ) ≠ -1 := by
          intro h
          apply hkn
          omega
        simp [hexp, Polynomial.coeff_monomial, hkn]

private theorem constantCoeff_aeval_of_constantCoeff_zero {B : K⟦X⟧}
    (hB0 : PowerSeries.constantCoeff B = 0) (p : K[X]) :
    PowerSeries.constantCoeff (Polynomial.aeval B p) = p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
      cases k with
      | zero => simp [Polynomial.aeval_def]
      | succ k =>
          simp [Polynomial.aeval_def, hB0, pow_succ]

private theorem coe_polynomial_aeval (B : K⟦X⟧) (p : K[X]) :
    ((Polynomial.aeval B p : K⟦X⟧) : K⸨X⸩) =
      Polynomial.aeval (B : K⸨X⸩) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
      simp only [aeval_monomial, algebraMap_eq, map_mul, HahnSeries.ofPowerSeries_C,
        HahnSeries.C_apply, map_pow, HahnSeries.single_zero_mul_eq_smul]
      rw [LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul]

/-- Formal one-variable Lagrange inversion over a field of characteristic zero, for a polynomial
kernel. -/
theorem lagrange_inversion_coeff [CharZero K] (φ : K[X])
    (hφ0 : φ.coeff 0 = 1) (B : K⟦X⟧)
    (hfix : B = PowerSeries.X * Polynomial.aeval B φ)
    (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n B = (φ ^ n).coeff (n - 1) / n := by
  let P : K⟦X⟧ := Polynomial.aeval B φ
  let Q : K⟦X⟧ := Polynomial.aeval B φ.derivative
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    calc
      PowerSeries.constantCoeff B =
          PowerSeries.constantCoeff
            (PowerSeries.X * Polynomial.aeval B φ) :=
        congrArg PowerSeries.constantCoeff hfix
      _ = 0 := by simp
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    rw [show P = Polynomial.aeval B φ by rfl,
      constantCoeff_aeval_of_constantCoeff_zero hB0, hφ0]
  have hB1 : PowerSeries.coeff 1 B = 1 := by
    calc
      PowerSeries.coeff 1 B =
          PowerSeries.coeff 1
            (PowerSeries.X * Polynomial.aeval B φ) :=
        congrArg (PowerSeries.coeff 1) hfix
      _ = PowerSeries.constantCoeff (Polynomial.aeval B φ) := by
        rw [show 1 = 0 + 1 by omega, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_zero_eq_constantCoeff_apply]
      _ = φ.coeff 0 := constantCoeff_aeval_of_constantCoeff_zero hB0 φ
      _ = 1 := hφ0
  have hPne : (P : K⸨X⸩) ≠ 0 := by
    intro h
    have hzero : P = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      simpa using h
    rw [hzero] at hP0
    norm_num at hP0
  have hSne : (HahnSeries.single (1 : ℤ) (1 : K) : K⸨X⸩) ≠ 0 := by
    simp
  have hfixP : B = PowerSeries.X * P := by exact hfix
  have hfixls :
      (B : K⸨X⸩) =
        HahnSeries.single (1 : ℤ) 1 * (P : K⸨X⸩) := by
    calc
      (B : K⸨X⸩) = ((PowerSeries.X * P : K⟦X⟧) : K⸨X⸩) := by
        rw [← hfixP]
      _ = _ := by rw [PowerSeries.coe_mul, PowerSeries.coe_X]
  have hderiv :
      (d⁄dX) B =
        P + PowerSeries.X * (Q * (d⁄dX) B) := by
    calc
      (d⁄dX) B =
          (d⁄dX) (PowerSeries.X * Polynomial.aeval B φ) := by
            rw [← hfix]
      _ = _ := by
        rw [Derivation.leibniz, Derivation.map_aeval]
        simp only [PowerSeries.derivative_X, smul_eq_mul, mul_one]
        change
          PowerSeries.X * (Q * (d⁄dX) B) + P =
            P + PowerSeries.X * (Q * (d⁄dX) B)
        ring
  have hderivls :
      (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
        (P : K⸨X⸩) + HahnSeries.single (1 : ℤ) 1 *
          ((Q : K⸨X⸩) * (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by
    calc
      (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
          ((P + PowerSeries.X * (Q * (d⁄dX) B) : K⟦X⟧) : K⸨X⸩) := by
            rw [← hderiv]
      _ = _ := by
        rw [PowerSeries.coe_add, PowerSeries.coe_mul, PowerSeries.coe_X,
          PowerSeries.coe_mul]
  have hpower (m : ℕ) :
      (B : K⸨X⸩) ^ (-((m : ℕ) : ℤ)) * (P : K⸨X⸩) ^ m =
        (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((m : ℕ) : ℤ)) := by
    rw [← zpow_natCast]
    rw [hfixls, mul_zpow]
    calc
      ((HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((m : ℕ) : ℤ)) *
            (P : K⸨X⸩) ^ (-((m : ℕ) : ℤ))) *
          (P : K⸨X⸩) ^ (m : ℤ) =
          (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((m : ℕ) : ℤ)) *
            ((P : K⸨X⸩) ^ (-((m : ℕ) : ℤ)) *
              (P : K⸨X⸩) ^ (m : ℤ)) := by ring
      _ = _ := by
        rw [← zpow_add₀ hPne]
        norm_num
  have hshift :
      (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
          (-((n - 1 : ℕ) : ℤ)) =
        (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) *
          HahnSeries.single (1 : ℤ) 1 := by
    rw [← zpow_add_one₀ hSne]
    congr 1
    omega
  have hrhs :
      (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
          (-((n + 1 : ℕ) : ℤ)) * (B : K⸨X⸩) =
        (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) *
          (P : K⸨X⸩) := by
    rw [hfixls, ← mul_assoc]
    congr 1
    rw [← zpow_add_one₀ hSne]
    congr 1
    omega
  have hderivSub :
      (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) -
          HahnSeries.single (1 : ℤ) 1 * (Q : K⸨X⸩) *
            (((d⁄dX) B : K⟦X⟧) : K⸨X⸩) =
        (P : K⸨X⸩) := by
    nth_rewrite 1 [hderivls]
    ring
  have hH :
      (((B : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) * (P : K⸨X⸩) ^ n -
            (B : K⸨X⸩) ^ (-((n - 1 : ℕ) : ℤ)) *
              (P : K⸨X⸩) ^ (n - 1) * (Q : K⸨X⸩)) *
          (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
        (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
          (-((n + 1 : ℕ) : ℤ)) * (B : K⸨X⸩) := by
    rw [hpower n, hpower (n - 1), hshift, hrhs]
    calc
      _ = (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) *
          ((((d⁄dX) B : K⟦X⟧) : K⸨X⸩) -
            HahnSeries.single (1 : ℤ) 1 * (Q : K⸨X⸩) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by ring
      _ = _ := by rw [hderivSub]
  by_cases hn1 : n = 1
  · subst n
    simp [hB1, hφ0]
  · have hn2 : 2 ≤ n := by omega
    have hEvalP :
        Polynomial.aeval (B : K⸨X⸩) φ = (P : K⸨X⸩) := by
      exact (coe_polynomial_aeval B φ).symm
    have hEvalQ :
        Polynomial.aeval (B : K⸨X⸩) φ.derivative = (Q : K⸨X⸩) := by
      exact (coe_polynomial_aeval B φ.derivative).symm
    have hR1 :
        residue
            (((B : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) *
              (P : K⸨X⸩) ^ n) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
          (φ ^ n).coeff (n - 1) := by
      have h := residue_shifted_aeval_mul_derivative hB0 hB1
        (φ ^ n) (n - 1)
      rw [show n - 1 + 1 = n by omega, map_pow, hEvalP] at h
      exact h
    have hR2 :
        residue
            ((((B : K⸨X⸩) ^ (-((n - 1 : ℕ) : ℤ)) *
                (P : K⸨X⸩) ^ (n - 1)) * (Q : K⸨X⸩)) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
          (φ ^ (n - 1) * φ.derivative).coeff (n - 2) := by
      have h := residue_shifted_aeval_mul_derivative hB0 hB1
        (φ ^ (n - 1) * φ.derivative) (n - 2)
      rw [show n - 2 + 1 = n - 1 by omega, map_mul, map_pow,
        hEvalP, hEvalQ] at h
      simpa only [mul_assoc] using h
    have hsplit :
        (((B : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) * (P : K⸨X⸩) ^ n -
              (B : K⸨X⸩) ^ (-((n - 1 : ℕ) : ℤ)) *
                (P : K⸨X⸩) ^ (n - 1) * (Q : K⸨X⸩)) *
            (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) =
          (((B : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) * (P : K⸨X⸩) ^ n) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) -
            ((((B : K⸨X⸩) ^ (-((n - 1 : ℕ) : ℤ)) *
                (P : K⸨X⸩) ^ (n - 1)) * (Q : K⸨X⸩)) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := by ring
    have hsingle :
        (HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
            (-((n + 1 : ℕ) : ℤ)) =
          HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 := by
      rw [zpow_neg, zpow_natCast, HahnSeries.single_pow,
        HahnSeries.inv_single]
      norm_num
    have hcoeffResidue :
        PowerSeries.coeff n B =
          residue
            ((HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
              (-((n + 1 : ℕ) : ℤ)) * (B : K⸨X⸩)) := by
      rw [hsingle]
      exact (residue_single_neg_succ_mul_coe n B).symm
    have hpoly := congrArg (fun p : K[X] => p.coeff (n - 2))
      (Polynomial.derivative_pow φ n)
    change (Polynomial.derivative (φ ^ n)).coeff (n - 2) =
      (Polynomial.C (n : K) * φ ^ (n - 1) * φ.derivative).coeff (n - 2) at hpoly
    rw [Polynomial.coeff_derivative] at hpoly
    have hidx : n - 2 + 1 = n - 1 := by omega
    rw [hidx] at hpoly
    simp only [Polynomial.coeff_C_mul, mul_assoc] at hpoly
    have hcast : ((n - 2 : ℕ) : K) + 1 = n - 1 := by
      exact_mod_cast hidx
    rw [hcast] at hpoly
    have hnne : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hformula :
        (φ ^ n).coeff (n - 1) -
            (φ ^ (n - 1) * φ.derivative).coeff (n - 2) =
          (φ ^ n).coeff (n - 1) / n := by
      rw [eq_div_iff hnne]
      linear_combination hpoly
    have hres := congrArg residue hH
    calc
      PowerSeries.coeff n B =
          residue
            ((HahnSeries.single (1 : ℤ) 1 : K⸨X⸩) ^
              (-((n + 1 : ℕ) : ℤ)) * (B : K⸨X⸩)) := hcoeffResidue
      _ = residue
            (((B : K⸨X⸩) ^ (-((n : ℕ) : ℤ)) * (P : K⸨X⸩) ^ n -
                (B : K⸨X⸩) ^ (-((n - 1 : ℕ) : ℤ)) *
                  (P : K⸨X⸩) ^ (n - 1) * (Q : K⸨X⸩)) *
              (((d⁄dX) B : K⟦X⟧) : K⸨X⸩)) := hres.symm
      _ = (φ ^ n).coeff (n - 1) -
            (φ ^ (n - 1) * φ.derivative).coeff (n - 2) := by
              rw [hsplit, residue_sub, hR1, hR2]
      _ = (φ ^ n).coeff (n - 1) / n := hformula

end PowerSeries
