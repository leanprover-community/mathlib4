/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.Analysis.Complex.WeierstrassFactor
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ` of points:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

and proves uniform convergence on compact sets assuming the standard summability hypothesis
`Summable (fun n => ‖a n‖⁻¹ ^ (m+1))`.

## Implementation notes

The summability hypothesis implies `‖a n‖ → ∞`, so the product converges locally uniformly on `ℂ`.
We phrase the main theorem as a `TendstoUniformlyOn` statement for the finite partial products.

## Main definitions

- `Complex.canonicalProduct`: the infinite product `∏' n, E_m(z / a n)`

## Main results

- `Complex.canonicalProduct_converges_uniformOn_compact`: uniform convergence on compact sets under
  the standard summability hypothesis and `a n ≠ 0`

-/

noncomputable section

@[expose] public section

open Complex Real Set Filter Topology
open scoped BigOperators Topology

namespace Complex

/-! ## Canonical product definition -/

/-- The canonical product `∏' n, E_m(z/a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

/-! ## Uniform convergence on compact sets

We keep this statement minimal: it is purely a convergence+analyticity lemma for the canonical
product, parameterized by a sequence `a` and a genus `m`.
-/

/-- Under the standard summability hypothesis `Summable (fun n => ‖a n‖⁻¹ ^ (m + 1))` and
`a n ≠ 0`, the finite partial products of `weierstrassFactor m (z / a n)` converge uniformly on
compact sets to `canonicalProduct m a`. -/
theorem canonicalProduct_converges_uniformOn_compact
    {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (canonicalProduct m a) atTop K := by
  classical
  intro K hK
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
  have hKU : K ⊆ U := by
    intro z hzK
    have hzle : ‖z‖ ≤ R := le_trans (hR0 z hzK) (le_max_left _ _)
    have hzlt : ‖z‖ < R + 1 := lt_of_le_of_lt hzle (by linarith)
    simpa [U, Metric.mem_ball, dist_zero_right] using hzlt
  let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / a n) - 1
  let u : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * (R + 1) ^ (m + 1))
  have hR1pos : 0 < R + 1 := by
    have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (by linarith [le_max_right R0 1])
  have h_tend : Tendsto (fun n => ‖a n‖⁻¹ ^ (m + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hRhalf_pos : 0 < (1 / (2 * (R + 1))) ^ (m + 1) := by
    have : 0 < (1 / (2 * (R + 1)) : ℝ) := by
      have : 0 < (2 * (R + 1) : ℝ) := by nlinarith [hR1pos]
      exact one_div_pos.mpr this
    exact pow_pos this (m + 1)
  have hLarge : ∀ᶠ n in atTop, (2 * (R + 1) : ℝ) ≤ ‖a n‖ := by
    have hEv := h_tend.eventually (eventually_lt_nhds hRhalf_pos)
    filter_upwards [hEv] with n hn
    by_contra h'
    have hle : ‖a n‖ ≤ 2 * (R + 1) := le_of_not_ge h'
    have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
    have hinv : (1 / (2 * (R + 1) : ℝ)) ≤ ‖a n‖⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le ha_pos hle)
    have hinv_pow :
        (1 / (2 * (R + 1) : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) hinv (m + 1)
    exact (not_lt_of_ge hinv_pow) (by simpa [one_div] using hn)
  have hBoundK : ∀ᶠ n in atTop, ∀ z ∈ K, ‖f n z‖ ≤ u n := by
    filter_upwards [hLarge] with n hn z hzK
    have hzU' : ‖z‖ < R + 1 := by
      have : z ∈ U := hKU hzK
      simpa [U, Metric.mem_ball, dist_zero_right] using this
    have hz_div : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
      have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp
      rw [this]
      have : ‖z‖ / ‖a n‖ ≤ (R + 1) / (2 * (R + 1)) := by
        have hnum : ‖z‖ ≤ R + 1 := le_of_lt hzU'
        have hdiv1 : ‖z‖ / ‖a n‖ ≤ (R + 1) / ‖a n‖ :=
          div_le_div_of_nonneg_right hnum (le_of_lt ha_pos)
        have hden2 : 0 < (2 * (R + 1) : ℝ) := by nlinarith [hR1pos]
        have hinv : (1 / ‖a n‖) ≤ 1 / (2 * (R + 1)) := by
          exact (one_div_le_one_div_of_le hden2 hn).trans_eq (by simp [one_div])
        have hdiv2 : (R + 1) / ‖a n‖ ≤ (R + 1) / (2 * (R + 1)) := by
          have hR1_nonneg : 0 ≤ (R + 1 : ℝ) := by linarith
          simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hinv hR1_nonneg)
        exact le_trans hdiv1 hdiv2
      have hfrac : (R + 1) / (2 * (R + 1)) = (1 / 2 : ℝ) := by
        field_simp [(ne_of_gt hR1pos)]
      simpa [hfrac] using this
    have hE :
        ‖weierstrassFactor m (z / a n) - 1‖ ≤ 4 * ‖z / a n‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a n) hz_div
    have hz_le : ‖z / a n‖ ≤ (R + 1) * ‖a n‖⁻¹ := by
      have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
      have : ‖z / a n‖ = ‖z‖ * ‖a n‖⁻¹ := by
        simp [div_eq_mul_inv]
      rw [this]
      have : ‖z‖ ≤ R + 1 := le_of_lt hzU'
      gcongr
    have hz_pow :
        ‖z / a n‖ ^ (m + 1) ≤ ((R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1)) := by
      have hz_pow' : ‖z / a n‖ ^ (m + 1) ≤ ((R + 1) * ‖a n‖⁻¹) ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) hz_le (m + 1)
      simpa [mul_pow] using hz_pow'
    dsimp [f, u]
    have : ‖weierstrassFactor m (z / a n) - 1‖ ≤
        (4 * (R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1)) := by
      nlinarith [hE, hz_pow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hcts : ∀ n, ContinuousOn (f n) K := by
    intro n
    have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / a n)) := by
      simpa [weierstrassFactor, partialLogSum] using (by
        continuity : Continuous fun z : ℂ =>
          ((1 : ℂ) - (z / a n)) * Complex.exp (partialLogSum m (z / a n)))
    simpa [f] using hcont.continuousOn.sub continuous_const.continuousOn
  have hprodK :
      HasProdUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) K := by
    simpa using Summable.hasProdUniformlyOn_nat_one_add (f := f) (K := K) hK hu hBoundK hcts
  have htendK :
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, (1 + f n z))
        (fun z => ∏' n, (1 + f n z)) atTop K :=
    (hasProdUniformlyOn_iff_tendstoUniformlyOn).1 hprodK
  have htendK' :
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (fun z => ∏' n, (1 + f n z)) atTop K :=
    htendK.congr <| Filter.Eventually.of_forall (fun s => by
      intro z hzK
      simp [f])
  refine htendK'.congr_right (fun z hzK => ?_)
  simp [f, canonicalProduct]

end Complex
