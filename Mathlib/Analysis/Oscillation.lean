/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Order.WellFoundedSet

/-!
# Oscillation

In this file we define the oscillation of a function `f: E → F` at a point `x` of `E`. (`E` is
required to be a TopologicalSpace and `F` a PseudoEMetricSpace.) The oscillation of `f` at `x` is
defined to be the infimum of `diam f '' N` for all neighborhoods `N` of `x`.

We also prove some simple facts about oscillation, most notably that the oscillation of `f`
at `x` is 0 if and only if `f` is continuous at `x`.

## Tags

oscillation
-/

open Topology EMetric

universe u v

variable {E : Type u} {F : Type v} [PseudoEMetricSpace F]

/-- The oscillation of `f : E → F` at `x`. -/
noncomputable def oscillation [TopologicalSpace E] (f : E → F) (x : E) : ENNReal :=
  ⨅ S ∈ (𝓝 x).map f, diam S

/-- The oscillation of `f` at `x` is 0 if and only if `f` is continuous at `x`. -/
theorem oscillation_zero_iff_continuousAt [TopologicalSpace E] (f : E → F) (x : E) :
    oscillation f x = 0 ↔ ContinuousAt f x := by
  constructor
  · intro hf
    rw [ContinuousAt, EMetric.tendsto_nhds]
    intro ε ε0
    simp only [← hf, oscillation, Filter.mem_map, gt_iff_lt, iInf_lt_iff, exists_prop] at ε0
    obtain ⟨S, hS, Sε⟩ := ε0
    refine Filter.mem_of_superset hS (fun y hy ↦ lt_of_le_of_lt ?_ Sε)
    exact edist_le_diam_of_mem (Set.mem_preimage.1 hy) <| Set.mem_preimage.1 (mem_of_mem_nhds hS)
  · intro hf
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (zero_le _)
    rw [zero_add]
    have : ball (f x) (ε / 2) ∈ (𝓝 x).map f := hf <| ball_mem_nhds _ (by simp [ne_of_gt hε])
    refine (biInf_le diam this).trans (le_of_le_of_eq diam_ball ?_)
    exact (ENNReal.mul_div_cancel' (by norm_num) (by norm_num))

/-- If `oscillation f x < ε` at every `x` in a compact set `K`, then there exists `δ > 0` such
that the oscillation of `f` on `ball x δ` is less than `ε` for every `x` in `K`. -/
theorem uniform_oscillation_of_compact [PseudoEMetricSpace E] {K : Set E} (comp : IsCompact K)
    {f : E → F} {ε : ENNReal} (hK : ∀ x ∈ K, oscillation f x < ε) :
    ∃ δ > 0, ∀ x ∈ K, diam (f '' (EMetric.ball x (ENNReal.ofReal δ))) ≤ ε := by
  let S := fun r ↦ { x : E | ∃ (a : ℝ), (a > r ∧ diam (f '' (ball x (ENNReal.ofReal a))) ≤ ε) }
  have S_open : ∀ r > 0, IsOpen (S r) := by
    intro r _
    rw [isOpen_iff_nhds]
    rintro x ⟨a, ar, ha⟩ t ht
    rw [EMetric.mem_nhds_iff]
    use ENNReal.ofReal ((a - r) / 2), by simp [ar]
    intro y hy
    apply ht
    use a - (a - r) / 2, by linarith
    refine le_trans (diam_mono (Set.image_mono fun z hz ↦ ?_)) ha
    rw [EMetric.mem_ball] at *
    refine lt_of_le_of_lt (edist_triangle z y x) (lt_of_lt_of_eq (ENNReal.add_lt_add hz hy) ?_)
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    simp
  have S_cover : K ⊆ ⋃ r > 0, S r := by
    intro x hx
    have : oscillation f x < ε := hK x hx
    simp only [oscillation, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := EMetric.mem_nhds_iff.1 hn₁
    simp only [gt_iff_lt, Set.mem_iUnion, exists_prop]
    have : ∀ r', (ENNReal.ofReal r') ≤ r → diam (f '' ball x (ENNReal.ofReal r')) ≤ ε := by
      intro r' hr'
      refine le_trans (diam_mono (subset_trans ?_ (Set.image_subset_iff.2 hr))) (le_of_lt hn₂)
      exact Set.image_mono (EMetric.ball_subset_ball hr')
    by_cases r_top : r = ⊤
    · use 1, one_pos, 2, one_lt_two, this 2 (by simp only [r_top, le_top])
    · obtain ⟨r', hr'⟩ := exists_between (ENNReal.toReal_pos (ne_of_gt r0) r_top)
      use r', hr'.1, ENNReal.toReal r, hr'.2, this r.toReal ENNReal.ofReal_toReal_le
  have S_antitone : ∀ (r₁ r₂ : ℝ), r₁ ≤ r₂ → S r₂ ⊆ S r₁ :=
    fun r₁ r₂ hr x ⟨a, ar₂, ha⟩ ↦ ⟨a, lt_of_le_of_lt hr ar₂, ha⟩
  have : ∃ r > 0, K ⊆ S r := by
    obtain ⟨T, Tb, Tfin, hT⟩ := comp.elim_finite_subcover_image S_open S_cover
    by_cases T_nonempty : T.Nonempty
    · use Tfin.isWF.min T_nonempty, Tb (Tfin.isWF.min_mem T_nonempty)
      intro x hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (hT hx)
      simp only [Set.mem_iUnion, exists_prop] at hr
      exact (S_antitone _ r (Set.IsWF.min_le Tfin.isWF T_nonempty hr.1)) hr.2
    · rw [Set.not_nonempty_iff_eq_empty] at T_nonempty
      use 1, one_pos, subset_trans hT (by simp [T_nonempty])
  obtain ⟨δ, δ0, hδ⟩ := this
  use δ, δ0
  intro x xK
  obtain ⟨a, δa, ha⟩ := hδ xK
  refine le_trans (diam_mono (Set.image_mono (ball_subset_ball ?_))) ha
  exact ENNReal.coe_le_coe.2 <| Real.toNNReal_mono (le_of_lt δa)
