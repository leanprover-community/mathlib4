/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The Second Main Theorem of Value Distribution Theory

This file will, in the future, establish the second main theorem of Value Distribution Theory. At
present, it collect material that will be used in the proof.

See Section VI.4 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion. A full formalized proof of the second main theorem is available at
https://github.com/kebekus/ProjectVD
-/

public section

open Finset

namespace Real

/-!
## The Separation Lemma

This section proves the pointwise **separation lemma**, over a general normed field.
-/

variable {𝕜 : Type*} [NormedField 𝕜]

/-
If `w` keeps distance at least `c` from every point of a finite set `s`, then
`∑ a ∈ s, log⁺ ‖w - a‖⁻¹` is bounded by `#s * log⁺ c⁻¹`.
-/
private lemma sum_posLog_inv_norm_sub_le {s : Finset 𝕜} {w : 𝕜} {c : ℝ} (hc : 0 < c)
    (h : ∀ a ∈ s, c ≤ ‖w - a‖) :
    ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ s.card * log⁺ c⁻¹ := by
  calc ∑ a ∈ s, log⁺ ‖w - a‖⁻¹
      ≤ ∑ a ∈ s, log⁺ c⁻¹ := by
        refine sum_le_sum fun a ha ↦ posLog_le_posLog (by positivity) ?_
        gcongr
        exact h a ha
    _ = s.card * log⁺ c⁻¹ := by rw [sum_const, nsmul_eq_mul]

/--
**Separation lemma**: for a finite set `s` of points, closeness to one point of `s`, measured by
`∑ a ∈ s, log⁺ ‖· - a‖⁻¹`, is detected by the single function `log⁺ ‖∑ a ∈ s, (· - a)⁻¹‖`, up to a
constant depending only on `s`.
-/
theorem exists_sum_posLog_inv_norm_sub_le (s : Finset 𝕜) :
    ∃ C, ∀ w : 𝕜, ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ + C := by
  -- If `w` is close to one point `a₀` of `s`, the singular term `(w - a₀)⁻¹` dominates the sum, so
  -- the single function `‖∑ a ∈ s, (· - a)⁻¹‖` detects closeness to *any* point of `s`; if `w` is
  -- far from all points of `s`, the left-hand side is bounded by a constant.
  classical
  rcases Nat.lt_or_ge s.card 2 with hcard | hcard
  · -- For `#s ≤ 1` the constant `0` works, the sums being empty or singletons.
    refine ⟨0, fun w ↦ ?_⟩
    have h : s.card = 0 ∨ s.card = 1 := by omega
    obtain h | h := h
    · rw [card_eq_zero] at h
      simp [h]
    · obtain ⟨a, rfl⟩ := card_eq_one.mp h
      simp [norm_inv]
  · -- Main case `2 ≤ #s`: take `δ` as the minimal gap of the target set, capped at `1`.
    obtain ⟨δ, hδ₀, hδ₁, hδgap⟩ :
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ ‖a - b‖ := by
      have hs : s.offDiag.Nonempty := by
        obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card_iff_nontrivial.mp hcard
        exact ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, hab⟩⟩
      refine ⟨min 1 (s.offDiag.inf' hs fun p ↦ dist p.1 p.2), lt_min one_pos ?_,
        min_le_left _ _, fun a ha b hb hab ↦ ?_⟩
      · rw [lt_inf'_iff]
        exact fun p hp ↦ dist_pos.mpr (mem_offDiag.mp hp).2.2
      · rw [← dist_eq_norm]
        have h1 : (s.offDiag.inf' hs fun p ↦ dist p.1 p.2) ≤ dist (a, b).1 (a, b).2 :=
          inf'_le _ (mem_offDiag.mpr ⟨ha, hb, hab⟩)
        exact (min_le_right _ _).trans h1
    have hq2 : (2 : ℝ) ≤ s.card := by exact_mod_cast hcard
    have h2q : (0 : ℝ) < 2 * s.card := by linarith
    have hlogq : 0 ≤ log s.card := log_nonneg (by linarith)
    have hposA : 0 ≤ log⁺ (2 * s.card / δ) := posLog_nonneg
    refine ⟨s.card * log⁺ (2 * s.card / δ) + log s.card, fun w ↦ ?_⟩
    by_cases! hfar : ∀ a ∈ s, δ / (2 * s.card) ≤ ‖w - a‖
    · -- Case (i): `w` keeps distance `δ/(2 #s)` from every point of `s`; then already the
      -- left-hand side is bounded by the constant.
      have h1 := sum_posLog_inv_norm_sub_le (div_pos hδ₀ h2q) hfar
      rw [inv_div] at h1
      have h2 : (0 : ℝ) ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := posLog_nonneg
      linarith
    · -- Case (ii): `w` is `δ/(2 #s)`-close to some `a₀ ∈ s`, hence `δ/2`-far from every
      -- other point of `s`.
      obtain ⟨a₀, ha₀, hnear⟩ := hfar
      have hcaste : ((s.erase a₀).card : ℝ) = (s.card : ℝ) - 1 := by
        rw [card_erase_of_mem ha₀, Nat.cast_sub (by omega), Nat.cast_one]
      have hother : ∀ b ∈ s.erase a₀, δ / 2 ≤ ‖w - b‖ := by
        intro b hb
        obtain ⟨hba₀, hbs⟩ := mem_erase.mp hb
        have h1 : δ ≤ ‖a₀ - b‖ := hδgap a₀ ha₀ b hbs (Ne.symm hba₀)
        have h2 : ‖a₀ - b‖ ≤ ‖a₀ - w‖ + ‖w - b‖ := by
          simpa [dist_eq_norm] using dist_triangle a₀ w b
        have h3 : ‖a₀ - w‖ < δ / (2 * s.card) := by rwa [norm_sub_rev]
        have h4 : δ / (2 * s.card) ≤ δ / 4 := by gcongr; linarith
        linarith
      -- Tail estimate: the sum over `s \ {a₀}` is bounded by the constant.
      have htail : ∑ b ∈ s.erase a₀, log⁺ ‖w - b‖⁻¹
          ≤ ((s.card : ℝ) - 1) * log⁺ (2 * s.card / δ) := by
        have h1 := sum_posLog_inv_norm_sub_le (by positivity) hother
        rw [inv_div, hcaste] at h1
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
        refine posLog_le_posLog (by positivity) ?_
        gcongr
        linarith
      -- Head estimate: the singular term `(w - a₀)⁻¹` dominates `∑ a ∈ s, (w - a)⁻¹`, so
      -- its `log⁺` is controlled by the right-hand side.
      have hhead : log⁺ ‖w - a₀‖⁻¹ ≤ log s.card + log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := by
        rcases eq_or_ne w a₀ with rfl | hne
        -- At `w = a₀` the junk-value convention gives `log⁺ ‖w - a₀‖⁻¹ = log⁺ 0⁻¹ = 0`.
        · simpa only [sub_self, norm_zero, inv_zero, posLog_zero]
            using add_nonneg hlogq posLog_nonneg
        · have hpos : 0 < ‖w - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
          -- The singular term is large …
          have hlarge : 2 * s.card / δ ≤ ‖w - a₀‖⁻¹ := by
            rw [← inv_div]
            gcongr
          -- … while the remaining terms are uniformly bounded …
          have htv : ‖∑ b ∈ s.erase a₀, (w - b)⁻¹‖ ≤ ((s.card : ℝ) - 1) * (2 / δ) := by
            calc ‖∑ b ∈ s.erase a₀, (w - b)⁻¹‖
                ≤ ∑ b ∈ s.erase a₀, ‖(w - b)⁻¹‖ := norm_sum_le _ _
              _ ≤ ∑ b ∈ s.erase a₀, 2 / δ := by
                  refine sum_le_sum fun b hb ↦ ?_
                  rw [norm_inv, ← inv_div]
                  gcongr
                  exact hother b hb
              _ = ((s.card : ℝ) - 1) * (2 / δ) := by
                  rw [sum_const, nsmul_eq_mul, hcaste]
          -- … so the full sum has norm at least `‖w - a₀‖⁻¹ / #s`.
          have hlow : ‖w - a₀‖⁻¹ - ((s.card : ℝ) - 1) * (2 / δ)
              ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ := by
            have h5 : ‖(w - a₀)⁻¹‖
                ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ + ‖∑ b ∈ s.erase a₀, (w - b)⁻¹‖ := by
              rw [← add_sum_erase s (fun a ↦ (w - a)⁻¹) ha₀]
              simpa using norm_sub_le ((w - a₀)⁻¹ + ∑ b ∈ s.erase a₀, (w - b)⁻¹)
                (∑ b ∈ s.erase a₀, (w - b)⁻¹)
            rw [norm_inv] at h5
            linarith
          have hdom : ‖w - a₀‖⁻¹ ≤ s.card * ‖∑ a ∈ s, (w - a)⁻¹‖ := by
            have h7 : (s.card : ℝ) * (2 / δ) = 2 * s.card / δ := by ring
            nlinarith [mul_le_mul_of_nonneg_left hlow
                (by linarith : (0 : ℝ) ≤ (s.card : ℝ)),
              mul_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ) - 1)
                (by linarith : (0 : ℝ) ≤ ‖w - a₀‖⁻¹ - (s.card : ℝ) * (2 / δ))]
          calc log⁺ ‖w - a₀‖⁻¹
              ≤ log⁺ (s.card * ‖∑ a ∈ s, (w - a)⁻¹‖) :=
                posLog_le_posLog (by positivity) hdom
            _ ≤ log s.card + log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := posLog_nat_mul
      -- Assemble the two estimates.
      rw [← add_sum_erase s (fun a ↦ log⁺ ‖w - a‖⁻¹) ha₀]
      have h6 : ((s.card : ℝ) - 1) * log⁺ (2 * s.card / δ)
          ≤ s.card * log⁺ (2 * s.card / δ) :=
        mul_le_mul_of_nonneg_right (by linarith) hposA
      linarith

end Real
