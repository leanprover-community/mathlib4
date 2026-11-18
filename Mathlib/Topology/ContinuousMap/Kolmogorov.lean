/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Kolmogorov's Criterion for Best Uniform Approximation in C(K)

This file establishes Kolmogorov's classical characterization of elements of best uniform
approximation (and the null layer of the metric projection) in the Banach space `C(K, ℝ)` of
continuous real-valued functions on a compact topological space `K`.

## Main results

* `ContinuousMap.kolmogorov_criterion_sufficiency`: if for every `v ∈ V` there exists a point
  `t ∈ K` where `|u t| = ‖u‖` and `u t * v t ≤ 0`, then `u` is a best uniform approximation
  error (`‖u‖ ≤ ‖u - w‖` for all `w ∈ V`).
* `ContinuousMap.kolmogorov_criterion_necessity`: conversely, on a nonempty compact space `K`,
  if `‖u‖ ≤ ‖u - w‖` for all `w ∈ V`, then for every `v ∈ V` there exists an extremal point
  `t ∈ K` with `|u t| = ‖u‖` and `u t * v t ≤ 0`.
* `ContinuousMap.kolmogorov_criterion_iff`: full equivalence on nonempty compact spaces.

## References

* E. S. Markov, *On Linear Metric Projections in Non-Reflexive Banach Spaces: Proximinal Lattices,
  Multivalued Boundaries and Linear Selections*, Zenodo (2026),
  [DOI: 10.5281/zenodo.24318041](https://doi.org).
* A. N. Kolmogorov, *A remark on the polynomials of P. L. Chebyshev deviating the least from a
  given function*, Uspekhi Mat. Nauk 3 (1948), 216–221.
-/

@[expose] public section

open Set Topology

namespace ContinuousMap

section Kolmogorov

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Kolmogorov's criterion (sufficiency):** in `C(K, ℝ)`, if for every `v ∈ V` there exists a
point `t ∈ K` attaining the supremum norm `|u t| = ‖u‖` with `u t * v t ≤ 0`, then `0` is a
best uniform approximation to `u` from `V`. -/
theorem kolmogorov_criterion_sufficiency (V : Submodule ℝ C(K, ℝ)) (u : C(K, ℝ))
    (h_kolm : ∀ v ∈ V, ∃ t : K, |u t| = ‖u‖ ∧ u t * v t ≤ 0) :
    ∀ w ∈ V, ‖u‖ ≤ ‖u - w‖ := by
  intro w hw
  rcases h_kolm w hw with ⟨t, ht_ext, ht_sign⟩
  have h1 : ‖u‖ ^ 2 ≤ (u t - w t) ^ 2 := by
    calc ‖u‖ ^ 2 = |u t| ^ 2 := by rw [ht_ext]
      _ = (u t) ^ 2 := sq_abs (u t)
      _ ≤ (u t) ^ 2 - 2 * (u t * w t) + (w t) ^ 2 := by
        have h_w2 : 0 ≤ (w t) ^ 2 := sq_nonneg (w t)
        linarith
      _ = (u t - w t) ^ 2 := by ring
  have h2 : |u t - w t| ≤ ‖u - w‖ := by
    have := norm_coe_le_norm (u - w) t
    simpa [Real.norm_eq_abs] using this
  have h3 : (u t - w t) ^ 2 ≤ ‖u - w‖ ^ 2 := by
    calc (u t - w t) ^ 2 = |u t - w t| ^ 2 := (sq_abs _).symm
      _ ≤ ‖u - w‖ ^ 2 := by nlinarith [abs_nonneg (u t - w t), norm_nonneg (u - w)]
  have h4 : ‖u‖ ^ 2 ≤ ‖u - w‖ ^ 2 := h1.trans h3
  nlinarith [norm_nonneg u, norm_nonneg (u - w)]

/-- **Kolmogorov's criterion (necessity):** on a nonempty compact space `K`, if `0` is a best
uniform approximation to `u` from `V`, then for every `v ∈ V` there exists an extremal point
`t ∈ K` with `|u t| = ‖u‖` and `u t * v t ≤ 0`. -/
theorem kolmogorov_criterion_necessity [Nonempty K] (V : Submodule ℝ C(K, ℝ)) (u : C(K, ℝ))
    (h_zero : ∀ w ∈ V, ‖u‖ ≤ ‖u - w‖) :
    ∀ v ∈ V, ∃ t : K, |u t| = ‖u‖ ∧ u t * v t ≤ 0 := by
  intro v hv
  by_cases hu0 : ‖u‖ = 0
  · obtain ⟨t₀⟩ := ‹Nonempty K›
    have hut₀ : u t₀ = 0 := by
      have h_le : |u t₀| ≤ 0 := by
        have := norm_coe_le_norm u t₀
        simpa [Real.norm_eq_abs, hu0] using this
      exact abs_nonpos_iff.mp h_le
    exact ⟨t₀, by simp [hu0, hut₀], by simp [hut₀]⟩
  · have hu_pos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
    by_contra h_neg
    push Not at h_neg
    let E : Set K := {t : K | |u t| = ‖u‖}
    have hE_closed : IsClosed E := isClosed_eq (continuous_abs.comp u.continuous) continuous_const
    have hE_comp : IsCompact E := hE_closed.isCompact
    have hE_ne : E.Nonempty := by
      rcases isCompact_univ.exists_isMaxOn univ_nonempty
        (continuous_abs.comp u.continuous).continuousOn with ⟨t_max, _, ht_max⟩
      refine ⟨t_max, le_antisymm ?_ ?_⟩
      · have := norm_coe_le_norm u t_max
        simpa [Real.norm_eq_abs] using this
      · rw [ContinuousMap.norm_le _ (abs_nonneg _)]
        intro t
        have h_le : |u t| ≤ |u t_max| := ht_max (mem_univ t)
        simpa [Real.norm_eq_abs] using h_le
    let f_sign : C(K, ℝ) :=
      ⟨fun t => u t * v t, u.continuous.mul v.continuous⟩
    rcases hE_comp.exists_isMinOn hE_ne f_sign.continuous.continuousOn with ⟨t₀, ht₀E, ht₀_min⟩
    have hm_pos : 0 < u t₀ * v t₀ := h_neg t₀ ht₀E
    let U_open : Set K := {t : K | (u t₀ * v t₀) / 2 < u t * v t}
    have hU_open : IsOpen U_open := isOpen_lt continuous_const f_sign.continuous
    have hE_sub_U : E ⊆ U_open := by
      intro t htE
      have h_le : u t₀ * v t₀ ≤ u t * v t := ht₀_min htE
      change (u t₀ * v t₀) / 2 < u t * v t
      linarith
    let F : Set K := U_openᶜ
    have hF_comp : IsCompact F := hU_open.isClosed_compl.isCompact
    have hv_pos : 0 < ‖v‖ := by
      by_contra hv0
      have hv_eq0 : ‖v‖ = 0 := le_antisymm (not_lt.mp hv0) (norm_nonneg v)
      have hv_zero : v = 0 := norm_eq_zero.mp hv_eq0
      simp [hv_zero] at hm_pos
    by_cases hF_ne : F.Nonempty
    · let g_abs : C(K, ℝ) := ⟨fun t => |u t|, continuous_abs.comp u.continuous⟩
      rcases hF_comp.exists_isMaxOn hF_ne g_abs.continuous.continuousOn with ⟨t₁, ht₁F, ht₁_max⟩
      have hM_lt : |u t₁| < ‖u‖ := by
        have h_le : |u t₁| ≤ ‖u‖ := by
          have := norm_coe_le_norm u t₁
          simpa [Real.norm_eq_abs] using this
        refine lt_of_le_of_ne h_le ?_
        intro h_eq
        exact ht₁F (hE_sub_U h_eq)
      let δ : ℝ := (‖u‖ - |u t₁|) / 2
      have hδ_pos : 0 < δ := by dsimp [δ]; linarith
      let m : ℝ := u t₀ * v t₀
      let lam : ℝ := min (δ / ‖v‖) (m / (2 * ‖v‖ ^ 2))
      have hlam_pos : 0 < lam := by
        apply lt_min
        · exact div_pos hδ_pos hv_pos
        · exact div_pos hm_pos (by positivity)
      have h_strict : ‖u - lam • v‖ < ‖u‖ := by
        rw [ContinuousMap.norm_lt_iff _ hu_pos]
        intro t
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
          Real.norm_eq_abs]
        by_cases htU : t ∈ U_open
        · change m / 2 < u t * v t at htU
          have h_lam_bound : lam ≤ m / (2 * ‖v‖ ^ 2) := min_le_right _ _
          have h_vt_bound : |v t| ≤ ‖v‖ := by
            have := norm_coe_le_norm v t
            simpa [Real.norm_eq_abs] using this
          have h_vt_sq : (v t) ^ 2 ≤ ‖v‖ ^ 2 := by
            calc (v t) ^ 2 = |v t| ^ 2 := (sq_abs _).symm
              _ ≤ ‖v‖ ^ 2 := by nlinarith [abs_nonneg (v t), norm_nonneg v]
          have h_ut_le : |u t| ≤ ‖u‖ := by
            have := norm_coe_le_norm u t
            simpa [Real.norm_eq_abs] using this
          have h_ut_sq : (u t) ^ 2 ≤ ‖u‖ ^ 2 := by
            calc (u t) ^ 2 = |u t| ^ 2 := (sq_abs _).symm
              _ ≤ ‖u‖ ^ 2 := by nlinarith [abs_nonneg (u t), norm_nonneg u]
          have h_cross : lam * (v t) ^ 2 < u t * v t := by
            calc lam * (v t) ^ 2 ≤ (m / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 :=
                  mul_le_mul h_lam_bound h_vt_sq (sq_nonneg _) (by positivity)
              _ = m / 2 := by field_simp
              _ < u t * v t := htU
          have h_sq_lt : (u t - lam * v t) ^ 2 < ‖u‖ ^ 2 := by
            have h_id : (u t - lam * v t) ^ 2 =
                (u t) ^ 2 - 2 * lam * (u t * v t - lam * (v t) ^ 2) - lam ^ 2 * (v t) ^ 2 := by
              ring
            have h_term1 : 0 < 2 * lam * (u t * v t - lam * (v t) ^ 2) := by nlinarith
            have h_term2 : 0 ≤ lam ^ 2 * (v t) ^ 2 := by positivity
            linarith
          have h_abs_sq : |u t - lam * v t| ^ 2 < ‖u‖ ^ 2 := by rwa [sq_abs]
          nlinarith [abs_nonneg (u t - lam * v t), hu_pos]
        · have htF : t ∈ F := htU
          have h_ut_le : |u t| ≤ |u t₁| := ht₁_max htF
          have h_lam_bound : lam ≤ δ / ‖v‖ := min_le_left _ _
          have h_vt_bound : |v t| ≤ ‖v‖ := by
            have := norm_coe_le_norm v t
            simpa [Real.norm_eq_abs] using this
          calc |u t - lam * v t| ≤ |u t| + |lam * v t| := abs_sub _ _
            _ = |u t| + lam * |v t| := by rw [abs_mul, abs_of_pos hlam_pos]
            _ ≤ |u t₁| + (δ / ‖v‖) * ‖v‖ := by gcongr
            _ = |u t₁| + δ := by rw [div_mul_cancel₀ _ hv_pos.ne']
            _ < ‖u‖ := by dsimp [δ]; linarith
      have h_mem_V : lam • v ∈ V := V.smul_mem lam hv
      have h_ge := h_zero (lam • v) h_mem_V
      linarith
    · rw [not_nonempty_iff_eq_empty] at hF_ne
      let m : ℝ := u t₀ * v t₀
      let lam : ℝ := m / (2 * ‖v‖ ^ 2)
      have hlam_pos : 0 < lam := div_pos hm_pos (by positivity)
      have h_strict : ‖u - lam • v‖ < ‖u‖ := by
        rw [ContinuousMap.norm_lt_iff _ hu_pos]
        intro t
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
          Real.norm_eq_abs]
        have htU : t ∈ U_open := by
          by_contra h_not
          have : t ∈ F := h_not
          rw [hF_ne] at this
          exact this
        change m / 2 < u t * v t at htU
        have h_vt_bound : |v t| ≤ ‖v‖ := by
          have := norm_coe_le_norm v t
          simpa [Real.norm_eq_abs] using this
        have h_vt_sq : (v t) ^ 2 ≤ ‖v‖ ^ 2 := by
          calc (v t) ^ 2 = |v t| ^ 2 := (sq_abs _).symm
            _ ≤ ‖v‖ ^ 2 := by nlinarith [abs_nonneg (v t), norm_nonneg v]
        have h_ut_le : |u t| ≤ ‖u‖ := by
          have := norm_coe_le_norm u t
          simpa [Real.norm_eq_abs] using this
        have h_ut_sq : (u t) ^ 2 ≤ ‖u‖ ^ 2 := by
          calc (u t) ^ 2 = |u t| ^ 2 := (sq_abs _).symm
            _ ≤ ‖u‖ ^ 2 := by nlinarith [abs_nonneg (u t), norm_nonneg u]
        have h_cross : lam * (v t) ^ 2 < u t * v t := by
          calc lam * (v t) ^ 2 = (m / (2 * ‖v‖ ^ 2)) * (v t) ^ 2 := rfl
            _ ≤ (m / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 :=
              mul_le_mul_of_nonneg_left h_vt_sq (by positivity)
            _ = m / 2 := by field_simp
            _ < u t * v t := htU
        have h_sq_lt : (u t - lam * v t) ^ 2 < ‖u‖ ^ 2 := by
          have h_id : (u t - lam * v t) ^ 2 =
              (u t) ^ 2 - 2 * lam * (u t * v t - lam * (v t) ^ 2) - lam ^ 2 * (v t) ^ 2 := by
            ring
          have h_term1 : 0 < 2 * lam * (u t * v t - lam * (v t) ^ 2) := by nlinarith
          have h_term2 : 0 ≤ lam ^ 2 * (v t) ^ 2 := by positivity
          linarith
        have h_abs_sq : |u t - lam * v t| ^ 2 < ‖u‖ ^ 2 := by rwa [sq_abs]
        nlinarith [abs_nonneg (u t - lam * v t), hu_pos]
      have h_mem_V : lam • v ∈ V := V.smul_mem lam hv
      have h_ge := h_zero (lam • v) h_mem_V
      linarith

/-- **Kolmogorov's criterion (full equivalence):** on a nonempty compact space `K`, `0` is a
best uniform approximation to `u` from `V` if and only if for every `v ∈ V` there exists
`t ∈ K` with `|u t| = ‖u‖` and `u t * v t ≤ 0`. -/
theorem kolmogorov_criterion_iff [Nonempty K] (V : Submodule ℝ C(K, ℝ)) (u : C(K, ℝ)) :
    (∀ w ∈ V, ‖u‖ ≤ ‖u - w‖) ↔ ∀ v ∈ V, ∃ t : K, |u t| = ‖u‖ ∧ u t * v t ≤ 0 :=
  ⟨kolmogorov_criterion_necessity V u, kolmogorov_criterion_sufficiency V u⟩

end Kolmogorov

end ContinuousMap
