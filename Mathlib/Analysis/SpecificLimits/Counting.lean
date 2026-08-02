/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Asymptotics of counting functions

If a sequence `f : ℕ → ℝ` grows linearly, `f n / n → τ` with `0 < τ`, and `c : ℝ → ℕ` counts
it, in the sense of the two one-sided bounds `t ≤ f (c t)` and `∀ k < c t, f k ≤ t`, then `c`
grows at the inverse rate: `c t / t → τ⁻¹` (`count_div_tendsto`). Monotonicity of `f` is not
required; the two bounds alone invert the rate.

`count_comp_div_tendsto` composes a Cesàro limit `S n / n → L` with such a count:
`S (c t) / t → L * ρ` whenever `c t / t → ρ` and `c → ∞`.

## Main results

* `count_div_tendsto`: a counting function of a linearly growing sequence grows at the
  inverse rate.
* `count_comp_div_tendsto`: Cesàro averages compose with a linearly growing count.
* `count_tendsto_atTop`: a counting function dominated below through `f` diverges.

## Tags

counting function, Cesaro average, specific limit
-/

@[expose] public section

open Filter

/-- A counting function dominated below through `f` diverges: if `t ≤ f (c t)` for every `t`,
then `c` leaves every finite prefix, because `f` is bounded on it. -/
theorem count_tendsto_atTop {f : ℕ → ℝ} {c : ℝ → ℕ} (hub : ∀ t, t ≤ f (c t)) :
    Tendsto c atTop atTop := by
  rw [tendsto_atTop]
  intro M
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ k < M, f k < T := by
    refine ⟨1 + ∑ j ∈ Finset.range M, |f j|, fun k hk ↦ ?_⟩
    have h1 : f k ≤ |f k| := le_abs_self _
    have h2 : |f k| ≤ ∑ j ∈ Finset.range M, |f j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (f j)) (Finset.mem_range.mpr hk)
    linarith
  filter_upwards [eventually_ge_atTop T] with t ht
  by_contra hcM
  exact absurd (hub t) (not_le.mpr ((hT _ (not_le.mp hcM)).trans_le ht))

/-- **Rate inversion for counting functions.** If `f n / n → τ` with `0 < τ` and `c` satisfies
the two one-sided bounds — `t` never exceeds `f` at the count, and `f` below the count never
exceeds `t` — then `c t / t → τ⁻¹`. `f` need not be monotone. The proof squeezes `t / c t`
between `f (c t - 1) / c t` and `f (c t) / c t`, both converging to `τ` by composition, and
inverts. -/
theorem count_div_tendsto {f : ℕ → ℝ} {c : ℝ → ℕ} {τ : ℝ} (hτ : 0 < τ)
    (hf : Tendsto (fun n ↦ f n / n) atTop (nhds τ)) (hub : ∀ t, t ≤ f (c t))
    (hlb : ∀ t, ∀ k < c t, f k ≤ t) :
    Tendsto (fun t ↦ (c t : ℝ) / t) atTop (nhds τ⁻¹) := by
  have hc_top : Tendsto c atTop atTop := count_tendsto_atTop hub
  have hupper : Tendsto (fun t ↦ f (c t) / (c t : ℝ)) atTop (nhds τ) := hf.comp hc_top
  have hg : Tendsto (fun n : ℕ ↦ f (n - 1) / n) atTop (nhds τ) := by
    have hpred : Tendsto (fun n : ℕ ↦ ((n - 1 : ℕ) : ℝ) / n) atTop (nhds 1) := by
      have h := (tendsto_natCast_div_add_atTop (-1 : ℝ)).inv₀ one_ne_zero
      rw [inv_one] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [inv_div, Nat.cast_sub hn, Nat.cast_one, ← sub_eq_add_neg]
    have h1 : Tendsto (fun n : ℕ ↦ f (n - 1) / ((n - 1 : ℕ) : ℝ)) atTop (nhds τ) :=
      hf.comp (tendsto_sub_atTop_nat 1)
    have h2 := h1.mul hpred
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr (by omega : (n - 1 : ℕ) ≠ 0))]
  have hlower : Tendsto (fun t ↦ f (c t - 1) / (c t : ℝ)) atTop (nhds τ) := hg.comp hc_top
  have hmid : Tendsto (fun t ↦ t / (c t : ℝ)) atTop (nhds τ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · filter_upwards [hc_top.eventually_ge_atTop 1] with t hct
      exact div_le_div_of_nonneg_right (hlb t _ (by omega)) (Nat.cast_nonneg _)
    · exact Eventually.of_forall fun t ↦ div_le_div_of_nonneg_right (hub t) (Nat.cast_nonneg _)
  exact (hmid.inv₀ hτ.ne').congr fun t ↦ inv_div _ _

/-- Cesàro composition with a count: if the partial-sum averages converge, `S n / n → L`, and
the count grows linearly, `c t / t → ρ` with `c → ∞`, then `S (c t) / t → L * ρ`. -/
theorem count_comp_div_tendsto {S : ℕ → ℝ} {c : ℝ → ℕ} {L ρ : ℝ}
    (hS : Tendsto (fun n ↦ S n / n) atTop (nhds L))
    (hc : Tendsto (fun t ↦ (c t : ℝ) / t) atTop (nhds ρ))
    (hc_top : Tendsto c atTop atTop) :
    Tendsto (fun t ↦ S (c t) / t) atTop (nhds (L * ρ)) := by
  have h1 : Tendsto (fun t ↦ S (c t) / (c t : ℝ)) atTop (nhds L) := hS.comp hc_top
  have h2 := h1.mul hc
  refine h2.congr' ?_
  filter_upwards [hc_top.eventually_ge_atTop 1] with t hct
  rw [div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr (by omega : c t ≠ 0))]
