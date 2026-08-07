/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus using Claude Code
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.MetricSpace.Infsep

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
    ∑ a ∈ s, log⁺ ‖w - a‖⁻¹ ≤ #s * log⁺ c⁻¹ := by
  calc ∑ a ∈ s, log⁺ ‖w - a‖⁻¹
      ≤ ∑ a ∈ s, log⁺ c⁻¹ := by
        refine sum_le_sum fun a ha ↦ posLog_le_posLog (by positivity) ?_
        gcongr
        exact h a ha
    _ = #s * log⁺ c⁻¹ := by rw [sum_const, nsmul_eq_mul]

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
  obtain (rfl | ⟨a, rfl⟩ | hs) : s = ∅ ∨ (∃ a, s = {a}) ∨ s.Nontrivial := by
    grind [Finset.Nonempty.exists_eq_singleton_or_nontrivial]
  case inl | inr.inl => exact ⟨0, by simp⟩ -- For `#s ≤ 1` the constant `0` works.
  case inr.inr => -- Main case `2 ≤ #s`: take `δ` as the minimal separation in `s`, capped at `1`.
    obtain ⟨δ, hδ₀, hδ₁, hδgap⟩ :
        ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ ‖a - b‖ := by
      refine ⟨min 1 (s : Set 𝕜).infsep, lt_min zero_lt_one ?_, min_le_left .., ?_⟩
      · simpa [Finset.infsep_pos_iff_nontrivial]
      · refine fun a ha b hb hab ↦ ?_
        grw [min_le_right, ← dist_eq_norm]
        exact Set.le_edist_of_le_infsep ha hb hab le_rfl
    have hq2 : (2 : ℝ) ≤ #s := mod_cast hs.two_le_card
    have hlogq : 0 ≤ log #s := by positivity
    have hposA : 0 ≤ log⁺ (2 * #s / δ) := posLog_nonneg
    refine ⟨#s * log⁺ (2 * #s / δ) + log #s, fun w ↦ ?_⟩
    by_cases! hfar : ∀ a ∈ s, δ / (2 * #s) ≤ ‖w - a‖
    · -- Case (i): `w` keeps distance `δ/(2 #s)` from every point of `s`; then already the
      -- left-hand side is bounded by the constant.
      have h1 := sum_posLog_inv_norm_sub_le (by positivity) hfar
      rw [inv_div] at h1
      have h2 : 0 ≤ log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := posLog_nonneg
      linarith
    · -- Case (ii): `w` is `δ/(2 #s)`-close to some `a₀ ∈ s`, hence `δ/2`-far from every
      -- other point of `s`.
      obtain ⟨a₀, ha₀, hnear⟩ := hfar
      have hcaste : #(s.erase a₀) = (#s : ℝ) - 1 := by grind [Nat.cast_sub]
      have hother (b) (hb : b ∈ s.erase a₀) : δ / 2 ≤ ‖w - b‖ := by
        have h1 : δ / (2 * #s) ≤ δ / 4 := by
          gcongr
          linarith
        have h2 : δ ≤ ‖w - a₀‖ + ‖w - b‖ := hδgap a₀ ha₀ b (by grind) (by grind) |>.trans <| by
          simpa [norm_sub_rev] using norm_sub_le (w - a₀) (w - b)
        linarith
      -- Tail estimate: the sum over `s \ {a₀}` is bounded by the constant.
      have htail : ∑ b ∈ s.erase a₀, log⁺ ‖w - b‖⁻¹ ≤ (#s - 1) * log⁺ (2 * #s / δ) := by
        have h1 := sum_posLog_inv_norm_sub_le (by positivity) hother
        rw [inv_div, hcaste] at h1
        apply h1.trans
        gcongr <;> linarith
      -- Head estimate: the singular term `(w - a₀)⁻¹` dominates `∑ a ∈ s, (w - a)⁻¹`, so
      -- its `log⁺` is controlled by the right-hand side.
      have hhead : log⁺ ‖w - a₀‖⁻¹ ≤ log #s + log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := by
        rcases eq_or_ne w a₀ with rfl | hne
        -- At `w = a₀` the junk-value convention gives `log⁺ ‖w - a₀‖⁻¹ = log⁺ 0⁻¹ = 0`.
        · simpa only [sub_self, norm_zero, inv_zero, posLog_zero]
            using add_nonneg hlogq posLog_nonneg
        · have hpos : 0 < ‖w - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
          -- The singular term is large …
          have hlarge : 2 * #s / δ ≤ ‖w - a₀‖⁻¹ := by
            rw [← inv_div]
            gcongr
          -- … while the remaining terms are uniformly bounded …
          have htv := calc
            ‖∑ b ∈ s.erase a₀, (w - b)⁻¹‖ ≤ ∑ b ∈ s.erase a₀, ‖(w - b)⁻¹‖ := norm_sum_le _ _
            _ ≤ ∑ b ∈ s.erase a₀, 2 / δ := by
              refine sum_le_sum fun b hb ↦ ?_
              rw [norm_inv, ← inv_div]
              gcongr
              exact hother b hb
            _ = (#s - 1) * (2 / δ) := by
              rw [sum_const, nsmul_eq_mul, hcaste]
          -- … so the full sum has norm at least `‖w - a₀‖⁻¹ / #s`.
          have hlow : ‖w - a₀‖⁻¹ - (#s - 1) * (2 / δ) ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ := by
            have h5 : ‖w - a₀‖⁻¹ ≤ ‖∑ a ∈ s, (w - a)⁻¹‖ + ‖∑ b ∈ s.erase a₀, (w - b)⁻¹‖ := by
              simpa [← add_sum_erase s _ ha₀] using
                norm_sub_le ((w - a₀)⁻¹ + ∑ b ∈ s.erase a₀, (w - b)⁻¹) (∑ b ∈ s.erase a₀, (w - b)⁻¹)
            linarith
          have hdom : ‖w - a₀‖⁻¹ ≤ #s * ‖∑ a ∈ s, (w - a)⁻¹‖ := by
            have h7 : #s * (2 / δ) = 2 * #s / δ := by ring
            have h8 : 0 ≤ (#s - 1) * (‖w - a₀‖⁻¹ - #s * (2 / δ)) := by
              apply mul_nonneg <;> linarith
            nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ #s)]
          calc log⁺ ‖w - a₀‖⁻¹ ≤ log⁺ (#s * ‖∑ a ∈ s, (w - a)⁻¹‖) := by gcongr
            _ ≤ log #s + log⁺ ‖∑ a ∈ s, (w - a)⁻¹‖ := posLog_nat_mul
      -- Assemble the two estimates.
      rw [← add_sum_erase s (fun a ↦ log⁺ ‖w - a‖⁻¹) ha₀]
      have h6 : (#s - 1) * log⁺ (2 * #s / δ) ≤ #s * log⁺ (2 * #s / δ) := by
        gcongr; linarith
      linarith

end Real
