/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.Data.ENNReal.Real
import Mathlib.Order.WellFoundedSet
import Mathlib.Topology.EMetricSpace.Diam

/-!
# Oscillation

In this file we define the oscillation of a function `f: E → F` at a point `x` of `E`. (`E` is
required to be a TopologicalSpace and `F` a PseudoEMetricSpace.) The oscillation of `f` at `x` is
defined to be the infimum of `diam f '' N` for all neighborhoods `N` of `x`. We also define
`oscillationWithin f D x`, which is the oscillation at `x` of `f` restricted to `D`.

We also prove some simple facts about oscillation, most notably that the oscillation of `f`
at `x` is 0 if and only if `f` is continuous at `x`, with versions for both `oscillation` and
`oscillationWithin`.

## Tags

oscillation, oscillationWithin
-/

open Topology EMetric Set ENNReal

universe u v

variable {E : Type u} {F : Type v} [PseudoEMetricSpace F]

/-- The oscillation of `f : E → F` at `x`. -/
noncomputable def oscillation [TopologicalSpace E] (f : E → F) (x : E) : ENNReal :=
  ⨅ S ∈ (𝓝 x).map f, diam S

/-- The oscillation of `f : E → F` within `D` at `x`. -/
noncomputable def oscillationWithin [TopologicalSpace E] (f : E → F) (D : Set E) (x : E) :
    ENNReal :=
  ⨅ S ∈ (𝓝[D] x).map f, diam S

/-- The oscillation of `f` at `x` within a neighborhood `D` of `x` is equal to `oscillation f x` -/
theorem oscillationWithin_nhds_eq_oscillation [TopologicalSpace E] (f : E → F) (D : Set E) (x : E)
    (hD : D ∈ 𝓝 x) : oscillationWithin f D x = oscillation f x := by
  rw [oscillation, oscillationWithin, nhdsWithin_eq_nhds.2 hD]

@[deprecated (since := "2025-05-22")]
alias oscillationWithin_nhd_eq_oscillation := oscillationWithin_nhds_eq_oscillation

/-- The oscillation of `f` at `x` within `univ` is equal to `oscillation f x` -/
theorem oscillationWithin_univ_eq_oscillation [TopologicalSpace E] (f : E → F) (x : E) :
    oscillationWithin f univ x = oscillation f x :=
  oscillationWithin_nhds_eq_oscillation f univ x Filter.univ_mem

namespace ContinuousWithinAt

theorem oscillationWithin_eq_zero [TopologicalSpace E] {f : E → F} {D : Set E}
    {x : E} (hf : ContinuousWithinAt f D x) : oscillationWithin f D x = 0 := by
  refine le_antisymm (_root_.le_of_forall_pos_le_add fun ε hε ↦ ?_) (zero_le _)
  rw [zero_add]
  have : ball (f x) (ε / 2) ∈ (𝓝[D] x).map f := hf <| ball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le diam this).trans (le_of_le_of_eq diam_ball ?_)
  exact (ENNReal.mul_div_cancel (by simp) (by simp))

end ContinuousWithinAt

namespace ContinuousAt

theorem oscillation_eq_zero [TopologicalSpace E] {f : E → F} {x : E} (hf : ContinuousAt f x) :
    oscillation f x = 0 := by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithin_univ_eq_oscillation f x ▸ hf.oscillationWithin_eq_zero

end ContinuousAt

namespace OscillationWithin

/-- The oscillation within `D` of `f` at `x ∈ D` is 0 if and only if `ContinuousWithinAt f D x`. -/
theorem eq_zero_iff_continuousWithinAt [TopologicalSpace E] (f : E → F) {D : Set E}
    {x : E} (xD : x ∈ D) : oscillationWithin f D x = 0 ↔ ContinuousWithinAt f D x := by
  refine ⟨fun hf ↦ EMetric.tendsto_nhds.mpr (fun ε ε0 ↦ ?_), fun hf ↦ hf.oscillationWithin_eq_zero⟩
  simp_rw [← hf, oscillationWithin, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy ↦ lt_of_le_of_lt ?_ Sε)
  exact edist_le_diam_of_mem (mem_preimage.1 hy) <| mem_preimage.1 (mem_of_mem_nhdsWithin xD hS)

end OscillationWithin

namespace Oscillation

/-- The oscillation of `f` at `x` is 0 if and only if `f` is continuous at `x`. -/
theorem eq_zero_iff_continuousAt [TopologicalSpace E] (f : E → F) (x : E) :
    oscillation f x = 0 ↔ ContinuousAt f x := by
  rw [← oscillationWithin_univ_eq_oscillation, ← continuousWithinAt_univ f x]
  exact OscillationWithin.eq_zero_iff_continuousWithinAt f (mem_univ x)

end Oscillation

namespace IsCompact

variable [PseudoEMetricSpace E] {K : Set E}
variable {f : E → F} {D : Set E} {ε : ENNReal}

/-- If `oscillationWithin f D x < ε` at every `x` in a compact set `K`, then there exists `δ > 0`
such that the oscillation of `f` on `ball x δ ∩ D` is less than `ε` for every `x` in `K`. -/
theorem uniform_oscillationWithin (comp : IsCompact K) (hK : ∀ x ∈ K, oscillationWithin f D x < ε) :
    ∃ δ > 0, ∀ x ∈ K, diam (f '' (ball x (ENNReal.ofReal δ) ∩ D)) ≤ ε := by
  let S := fun r ↦ { x : E | ∃ (a : ℝ), (a > r ∧ diam (f '' (ball x (ENNReal.ofReal a) ∩ D)) ≤ ε) }
  have S_open : ∀ r > 0, IsOpen (S r) := by
    refine fun r _ ↦ isOpen_iff.mpr fun x ⟨a, ar, ha⟩ ↦
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refine fun y hy ↦ ⟨a - (a - r) / 2, by linarith,
      le_trans (diam_mono (image_mono fun z hz ↦ ?_)) ha⟩
    refine ⟨lt_of_le_of_lt (edist_triangle z y x) (lt_of_lt_of_eq (ENNReal.add_lt_add hz.1 hy) ?_),
      hz.2⟩
    rw [← ofReal_add (by linarith) (by linarith), sub_add_cancel]
  have S_cover : K ⊆ ⋃ r > 0, S r := by
    intro x hx
    have : oscillationWithin f D x < ε := hK x hx
    simp only [oscillationWithin, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := mem_nhdsWithin_iff.1 hn₁
    simp only [gt_iff_lt, mem_iUnion, exists_prop]
    have : ∀ r', (ENNReal.ofReal r') ≤ r → diam (f '' (ball x (ENNReal.ofReal r') ∩ D)) ≤ ε := by
      intro r' hr'
      grw [← hn₂, ← image_subset_iff.2 hr, hr']
    by_cases r_top : r = ⊤
    · exact ⟨1, one_pos, 2, by simp, this 2 (by simp only [r_top, le_top])⟩
    · obtain ⟨r', hr'⟩ := exists_between (toReal_pos (ne_of_gt r0) r_top)
      use r', hr'.1, r.toReal, hr'.2, this r.toReal ofReal_toReal_le
  have S_antitone : ∀ (r₁ r₂ : ℝ), r₁ ≤ r₂ → S r₂ ⊆ S r₁ :=
    fun r₁ r₂ hr x ⟨a, ar₂, ha⟩ ↦ ⟨a, lt_of_le_of_lt hr ar₂, ha⟩
  obtain ⟨δ, δ0, hδ⟩ : ∃ r > 0, K ⊆ S r := by
    obtain ⟨T, Tb, Tfin, hT⟩ := comp.elim_finite_subcover_image S_open S_cover
    by_cases T_nonempty : T.Nonempty
    · use Tfin.isWF.min T_nonempty, Tb (Tfin.isWF.min_mem T_nonempty)
      intro x hx
      obtain ⟨r, hr⟩ := mem_iUnion.1 (hT hx)
      simp only [mem_iUnion, exists_prop] at hr
      exact (S_antitone _ r (IsWF.min_le Tfin.isWF T_nonempty hr.1)) hr.2
    · rw [not_nonempty_iff_eq_empty] at T_nonempty
      use 1, one_pos, subset_trans hT (by simp [T_nonempty])
  use δ, δ0
  intro x xK
  obtain ⟨a, δa, ha⟩ := hδ xK
  grw [← ha]
  gcongr

/-- If `oscillation f x < ε` at every `x` in a compact set `K`, then there exists `δ > 0` such
that the oscillation of `f` on `ball x δ` is less than `ε` for every `x` in `K`. -/
theorem uniform_oscillation {K : Set E} (comp : IsCompact K)
    {f : E → F} {ε : ENNReal} (hK : ∀ x ∈ K, oscillation f x < ε) :
    ∃ δ > 0, ∀ x ∈ K, diam (f '' (ball x (ENNReal.ofReal δ))) ≤ ε := by
  simp only [← oscillationWithin_univ_eq_oscillation] at hK
  convert ← comp.uniform_oscillationWithin hK
  exact inter_univ _

end IsCompact
