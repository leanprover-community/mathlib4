/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Deligne's archimedean Gamma-factors

In the theory of L-series one frequently encounters the following functions (of a complex variable
`s`) introduced in Deligne's landmark paper *Valeurs de fonctions L et periodes d'integrales*:

$$ \Gamma_{\mathbb{R}}(s) = \pi ^ {-s / 2} \Gamma (s / 2) $$

and

$$ \Gamma_{\mathbb{C}}(s) = 2 (2 \pi) ^ {-s} \Gamma (s). $$

These are the factors that need to be included in the Dedekind zeta function of a number field
for each real, resp. complex, infinite place.

(Note that these are *not* the same as Mathlib's `Real.Gamma` vs. `Complex.Gamma`; Deligne's
functions both take a complex variable as input.)

This file defines these functions, and proves some elementary properties, including a reflection
formula which is an important input in functional equations of (un-completed) Dirichlet L-functions.
-/

open Filter Topology Asymptotics Real Set MeasureTheory
open Complex hiding abs_of_nonneg

namespace Complex

/-- Deligne's archimedean Gamma factor for a real infinite place.

See "Valeurs de fonctions L et periodes d'integrales" § 5.3. Note that this is not the same as
`Real.Gamma`; in particular it is a function `ℂ → ℂ`. -/
noncomputable def Gammaℝ (s : ℂ) := π ^ (-s / 2) * Gamma (s / 2)

lemma Gammaℝ_def (s : ℂ) : Gammaℝ s = π ^ (-s / 2) * Gamma (s / 2) := rfl

/-- Deligne's archimedean Gamma factor for a complex infinite place.

See "Valeurs de fonctions L et periodes d'integrales" § 5.3. (Some authors omit the factor of 2).
Note that this is not the same as `Complex.Gamma`. -/
noncomputable def Gammaℂ (s : ℂ) := 2 * (2 * π) ^ (-s) * Gamma s

lemma Gammaℂ_def (s : ℂ) : Gammaℂ s = 2 * (2 * π) ^ (-s) * Gamma s := rfl

lemma Gammaℝ_add_two {s : ℂ} (hs : s ≠ 0) : Gammaℝ (s + 2) = Gammaℝ s * s / 2 / π := by
  rw [Gammaℝ_def, Gammaℝ_def, neg_div, add_div, neg_add, div_self two_ne_zero,
    Gamma_add_one _ (div_ne_zero hs two_ne_zero),
    cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), cpow_neg_one]
  field_simp

lemma Gammaℂ_add_one {s : ℂ} (hs : s ≠ 0) : Gammaℂ (s + 1) = Gammaℂ s * s / 2 / π := by
  rw [Gammaℂ_def, Gammaℂ_def, Gamma_add_one _ hs, neg_add,
    cpow_add _ _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)), cpow_neg_one]
  field_simp

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gammaℝ s ≠ 0 := by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

lemma Gammaℝ_eq_zero_iff {s : ℂ} : Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n) := by
  simp [Gammaℝ_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff (two_ne_zero' ℂ), mul_comm]

@[simp]
lemma Gammaℝ_one : Gammaℝ 1 = 1 := by
  rw [Gammaℝ_def, Complex.Gamma_one_half_eq]
  simp [neg_div, cpow_neg, pi_ne_zero]

@[simp]
lemma Gammaℂ_one : Gammaℂ 1 = 1 / π := by
  rw [Gammaℂ_def, cpow_neg_one, Complex.Gamma_one]
  field_simp [pi_ne_zero]

section analyticity

lemma differentiable_Gammaℝ_inv : Differentiable ℂ (fun s ↦ (Gammaℝ s)⁻¹) := by
  conv => enter [2, s]; rw [Gammaℝ, mul_inv]
  refine Differentiable.mul (fun s ↦ .inv ?_ (by simp [pi_ne_zero])) ?_
  · refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  · exact differentiable_one_div_Gamma.comp (differentiable_id.div_const _)

lemma Gammaℝ_residue_zero : Tendsto (fun s ↦ s * Gammaℝ s) (𝓝[≠] 0) (𝓝 2) := by
  have h : Tendsto (fun z : ℂ ↦ z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const _).mono_left nhdsWithin_le_nhds,
      eventually_of_mem self_mem_nhdsWithin fun x hx ↦ div_ne_zero hx two_ne_zero⟩
  have h' : Tendsto (fun s : ℂ ↦ 2 * (π : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 2 = 𝓝 (2 * (π : ℂ) ^ (-(0 : ℂ) / 2)))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow (ofReal_ne_zero.mpr pi_ne_zero)).comp
      (continuousAt_id.neg.div_const _))
  convert mul_one (2 : ℂ) ▸ (h'.mul h) using 2 with z
  rw [Gammaℝ]
  ring_nf

end analyticity

section reflection

/-- Reformulation of the doubling formula in terms of `Gammaℝ`. -/
lemma Gammaℝ_mul_Gammaℝ_add_one (s : ℂ) : Gammaℝ s * Gammaℝ (s + 1) = Gammaℂ s := by
  simp only [Gammaℝ_def, Gammaℂ_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : ℂ)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), Complex.Gamma_mul_Gamma_add_half,
      sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_one, ofReal_ofNat]
    ring_nf
  _ = 2 * ((2 : ℝ) ^ (-s) * π ^ (-s)) * Gamma s := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one,
      ← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), ofReal_ofNat]
    ring_nf
  _ = 2 * (2 * π) ^ (-s) * Gamma s := by
    rw [← mul_cpow_ofReal_nonneg two_pos.le pi_pos.le, ofReal_ofNat]

/-- Reformulation of the reflection formula in terms of `Gammaℝ`. -/
lemma Gammaℝ_one_sub_mul_Gammaℝ_one_add (s : ℂ) :
    Gammaℝ (1 - s) * Gammaℝ (1 + s) = (cos (π * s / 2))⁻¹ :=
  calc Gammaℝ (1 - s) * Gammaℝ (1 + s)
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (1 - (1 - s) / 2)) := by
    simp only [Gammaℝ_def]
    ring_nf
  _ = (π ^ ((s - 1) / 2) * π ^ ((-1 - s) / 2) * π ^ (1 : ℂ)) / sin (π / 2 - π * s / 2) := by
    rw [Complex.Gamma_mul_Gamma_one_sub, cpow_one]
    ring_nf
  _ = _ := by
    simp_rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero),
      Complex.sin_pi_div_two_sub]
    ring_nf
    rw [cpow_zero, one_mul]

/-- Another formulation of the reflection formula in terms of `Gammaℝ`. -/
lemma Gammaℝ_div_Gammaℝ_one_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -(2 * n + 1)) :
    Gammaℝ s / Gammaℝ (1 - s) = Gammaℂ s * cos (π * s / 2) := by
  have : Gammaℝ (s + 1) ≠ 0 := by
    simpa only [Ne, Gammaℝ_eq_zero_iff, not_exists, ← eq_sub_iff_add_eq,
      sub_eq_add_neg, ← neg_add]
  calc Gammaℝ s / Gammaℝ (1 - s)
  _ = (Gammaℝ s * Gammaℝ (s + 1)) / (Gammaℝ (1 - s) * Gammaℝ (1 + s)) := by
    rw [add_comm 1 s, mul_comm (Gammaℝ (1 - s)) (Gammaℝ (s + 1)), ← div_div,
      mul_div_cancel_right₀ _ this]
  _ = (2 * (2 * π) ^ (-s) * Gamma s) / ((cos (π * s / 2))⁻¹) := by
    rw [Gammaℝ_one_sub_mul_Gammaℝ_one_add, Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def]
  _ = _ := by rw [Gammaℂ_def, div_eq_mul_inv, inv_inv]

/-- Formulation of reflection formula tailored to functional equations of L-functions of even
Dirichlet characters (including Riemann zeta). -/
lemma inv_Gammaℝ_one_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    (Gammaℝ (1 - s))⁻¹ = Gammaℂ s * cos (π * s / 2) * (Gammaℝ s)⁻¹ := by
  have h1 : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
    intro n h
    specialize hs (2 * n)
    simp_all
  have h2 : ∀ (n : ℕ), s ≠ -(2 * ↑n + 1) := by
    intro n h
    specialize hs (2 * n + 1)
    simp_all
  rw [← Gammaℝ_div_Gammaℝ_one_sub h2, ← div_eq_mul_inv, div_right_comm, div_self h1, one_div]

/-- Formulation of reflection formula tailored to functional equations of L-functions of odd
Dirichlet characters. -/
lemma inv_Gammaℝ_two_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    (Gammaℝ (2 - s))⁻¹ = Gammaℂ s * sin (π * s / 2) * (Gammaℝ (s + 1))⁻¹ := by
  by_cases h : s = 1
  · rw [h, (by ring : 2 - 1 = (1 : ℂ)), Gammaℝ_one, Gammaℝ,
    neg_div, (by simp : (1 + 1) / 2 = (1 : ℂ)), Complex.Gamma_one, Gammaℂ_one,
    mul_one, Complex.sin_pi_div_two, mul_one, cpow_neg_one, mul_one, inv_inv,
    div_mul_cancel₀ _ (ofReal_ne_zero.mpr pi_ne_zero), inv_one]
  rw [← Ne, ← sub_ne_zero] at h
  have h' (n : ℕ) : s - 1 ≠ -n := by
    rcases n with - | m
    · rwa [Nat.cast_zero, neg_zero]
    · rw [Ne, sub_eq_iff_eq_add]
      convert hs m using 2
      push_cast
      ring
  rw [(by ring : 2 - s = 1 - (s - 1)), inv_Gammaℝ_one_sub h',
    (by rw [sub_add_cancel] : Gammaℂ s = Gammaℂ (s - 1 + 1)), Gammaℂ_add_one h,
    (by ring : s + 1 = (s - 1) + 2), Gammaℝ_add_two h, mul_sub, sub_div, mul_one,
      Complex.cos_sub_pi_div_two]
  simp_rw [mul_div_assoc, mul_inv]
  generalize (Gammaℝ (s - 1))⁻¹ = A
  field_simp [pi_ne_zero]

end reflection

end Complex
