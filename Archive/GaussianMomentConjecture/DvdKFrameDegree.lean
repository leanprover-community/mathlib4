/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrame
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The degree leg of `hderiv`: the small-root factor contributes nothing to `[x⁰]`

This module supplies leg (c) of the `hderiv` identity. If `u` is a unit of
`(LaurentSeries F)⟦t⟧` whose constant `t`-coefficient is `1` and all of whose higher
`t`-coefficients are supported in strictly negative `x`-degrees, then the `x⁰`-coefficient of
`logDeriv u` vanishes.

Applied to the small-root factor `P` of the Weierstrass factorization `Φ = P * h`, this is the
statement that `[x⁰] (P_t / P) = 0`, which is what lets the disk/annulus split of `[x⁰]` isolate
the `h`-side contribution `d_t h(0, t) / h(0, t)`.
-/

open PowerSeries HahnSeries GMC2.DvdKFrame
open scoped Pointwise

namespace GMC2.DvdKFrameDegree

variable {F : Type*} [Field F]

/-- **(c) the degree lemma.** If `u : (LaurentSeries F)⟦t⟧` is a unit with `u.coeff 0 = 1` and every
higher `t`-coefficient supported on strictly negative `x`-degrees, then `xCoeff0 (logDeriv u) = 0`.
Proof: `logDeriv u · u = ∂u` (`logDeriv_mul_self`); strong induction on the `t`-order gives every
`t`-coefficient of `logDeriv u` a strictly-negative `x`-support, so its `x⁰` coefficient is `0`. -/
theorem xCoeff0_logDeriv_eq_zero (u : PowerSeries (LaurentSeries F)) (hu : IsUnit u)
    (h0 : coeff (R := LaurentSeries F) 0 u = 1)
    (hneg : ∀ n, 1 ≤ n → (coeff (R := LaurentSeries F) n u).support ⊆ Set.Iio 0) :
    xCoeff0 (logDeriv u) = 0 := by
  have hLu : logDeriv u * u = derivative _ u := logDeriv_mul_self hu
  have hIio : (Set.Iio (0:ℤ)) + (Set.Iio (0:ℤ)) ⊆ Set.Iio 0 := by
    rintro z ⟨a, ha, b, hb, rfl⟩; simp only [Set.mem_Iio] at *; omega
  -- every t-coefficient of logDeriv u has strictly negative x-support
  have key : ∀ k, (coeff (R := LaurentSeries F) k (logDeriv u)).support ⊆ Set.Iio 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hmul := congrArg (coeff (R := LaurentSeries F) k) hLu
      rw [PowerSeries.coeff_mul, coeff_derivative] at hmul
      -- isolate the (k,0) diagonal term (= coeff k (logDeriv u) since coeff 0 u = 1)
      have hmem : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k := by
        simp [Finset.HasAntidiagonal.mem_antidiagonal]
      rw [← Finset.add_sum_erase _ _ hmem] at hmul
      simp only [h0, mul_one] at hmul
      -- solve for coeff k (logDeriv u)
      have hsolve : coeff (R := LaurentSeries F) k (logDeriv u)
          = coeff (R := LaurentSeries F) (k + 1) u * (↑k + 1)
            - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (k, 0),
                coeff (R := LaurentSeries F) p.1 (logDeriv u)
                  * coeff (R := LaurentSeries F) p.2 u := by
        linear_combination hmul
      rw [hsolve]
      have hnc : ((↑k + 1 : LaurentSeries F)).support ⊆ {0} := by
        have : (↑k + 1 : LaurentSeries F) = HahnSeries.C ((↑k + 1 : F)) := by
          rw [map_add, map_natCast, map_one]
        rw [this]; exact HahnSeries.support_single_subset
      refine (support_sub_subset _ _).trans (Set.union_subset ?_ ?_)
      · -- support (coeff (k+1) u * (↑k+1)) ⊆ support (coeff (k+1) u) ⊆ Iio 0
        refine (support_mul_subset).trans ?_
        refine (Set.add_subset_add (hneg (k+1) (by omega)) hnc).trans ?_
        rintro z ⟨a, ha, b, hb, rfl⟩
        rw [Set.mem_singleton_iff] at hb; subst hb; simpa using ha
      · -- support of the sum ⊆ Iio 0
        refine Finset.sum_induction _ (fun s => HahnSeries.support s ⊆ Set.Iio 0)
          (fun a b ha hb => (HahnSeries.support_add_subset a b).trans (Set.union_subset ha hb))
          (by simp) ?_
        intro p hp
        have hp0 : p ∈ Finset.HasAntidiagonal.antidiagonal k := Finset.mem_of_mem_erase hp
        have hpne : p ≠ (k, 0) := Finset.ne_of_mem_erase hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp0
        have hb1 : 1 ≤ p.2 := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · exact absurd (Prod.ext (by omega) h) hpne
          · exact h
        have ha_lt : p.1 < k := by omega
        exact (support_mul_subset).trans
          ((Set.add_subset_add (ih p.1 ha_lt) (hneg p.2 hb1)).trans hIio)
  -- conclude xCoeff0 (logDeriv u) = 0
  ext k
  rw [coeff_xCoeff0, map_zero]
  by_contra hne
  exact absurd (key k (by rw [HahnSeries.mem_support]; exact hne)) (by simp)

/-- **(c), the frame-local degree lemma for a monic-degree-`M` factor.** If `φ` is a unit in
`(LaurentSeries F)⟦t⟧` with `φ.coeff 0 = xᴹ` (`= single M 1`) and every higher `t`-coefficient of
`x`-degree `< M`, then `xCoeff0 (logDeriv φ) = 0`. This is `[x⁰](logDeriv P) = 0` for the
Weierstrass distinguished factor `P` (monic of `x`-degree `M`, `P_t` of `x`-degree `< M`), the
remaining input to `hderiv` — via `φ = xᴹ·u` with `logDeriv xᴹ = 0` and `u` of the previous lemma's
shape. -/
theorem xCoeff0_logDeriv_eq_zero_of_monic (φ : PowerSeries (LaurentSeries F)) (hφ : IsUnit φ)
    (M : ℕ) (h0 : coeff (R := LaurentSeries F) 0 φ = HahnSeries.single (M : ℤ) 1)
    (hlt : ∀ n, 1 ≤ n → (coeff (R := LaurentSeries F) n φ).support ⊆ Set.Iio (M : ℤ)) :
    xCoeff0 (logDeriv φ) = 0 := by
  set xM : PowerSeries (LaurentSeries F) := PowerSeries.C (HahnSeries.single (M : ℤ) 1) with hxM
  set xnM : PowerSeries (LaurentSeries F) := PowerSeries.C (HahnSeries.single (-(M : ℤ)) 1)
    with hxnM
  have hxMxnM : xM * xnM = 1 := by
    rw [hxM, hxnM, ← map_mul, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
      ← HahnSeries.C_apply, HahnSeries.C_one, map_one]
  set u : PowerSeries (LaurentSeries F) := φ * xnM with hu_def
  have hxMunit : IsUnit xM := ⟨⟨xM, xnM, hxMxnM, by rw [mul_comm]; exact hxMxnM⟩, rfl⟩
  have hxnMunit : IsUnit xnM := ⟨⟨xnM, xM, by rw [mul_comm]; exact hxMxnM, hxMxnM⟩, rfl⟩
  have huunit : IsUnit u := hφ.mul hxnMunit
  have hφeq : φ = u * xM := by rw [hu_def, mul_assoc, mul_comm xnM xM, hxMxnM, mul_one]
  -- logDeriv xM = 0 (xM is constant in t)
  have hlogxM : logDeriv xM = 0 := by
    rw [PowerSeries.logDeriv, hxM, PowerSeries.derivative_C, zero_mul]
  -- u satisfies the previous lemma's hypotheses
  have hu0 : coeff (R := LaurentSeries F) 0 u = 1 := by
    rw [hu_def, hxnM, PowerSeries.coeff_mul_C, h0, HahnSeries.single_mul_single, add_neg_cancel,
      mul_one, ← HahnSeries.C_apply, HahnSeries.C_one]
  have huneg : ∀ n, 1 ≤ n → (coeff (R := LaurentSeries F) n u).support ⊆ Set.Iio 0 := by
    intro n hn
    rw [hu_def, hxnM, PowerSeries.coeff_mul_C]
    refine (HahnSeries.support_mul_subset).trans ?_
    refine (Set.add_subset_add (hlt n hn) HahnSeries.support_single_subset).trans ?_
    rintro z ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb; subst hb
    simp only [Set.mem_Iio] at *; omega
  rw [hφeq, PowerSeries.logDeriv_mul huunit hxMunit, hlogxM, add_zero]
  exact xCoeff0_logDeriv_eq_zero u huunit hu0 huneg


end GMC2.DvdKFrameDegree
