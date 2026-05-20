/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom, Lua Viana Reis
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Oscillation

In this file we define the oscillation of a function `f: E → F` along a filter `l` of `E`. (`F` is
required to be a PseudoEMetricSpace.) The oscillation of `f` at `l` is
defined to be the infimum of `diam f '' N` for all sets `N` in `l`. We also define
`oscillationWithin f D l`, which is the oscillation at `l` of `f` restricted to `D`.

We also prove some simple facts about oscillation, most notably that the oscillation of `f`
at `x` is 0 if and only if `f` is continuous at `x`, with versions for both `oscillation` and
`oscillationWithin`.

## Tags

oscillation, oscillationWithin
-/

@[expose] public section

open Topology Metric Set ENNReal Filter

universe u v

variable {E : Type u} {F : Type v} [PseudoEMetricSpace F]

/-- The oscillation of `f : E → F` along `l`. -/
noncomputable def oscillation (f : E → F) (l : Filter E) : ENNReal :=
  ⨅ S ∈ l.map f, ediam S

theorem oscillation_le_ediam_range {f : E → F} {l} : oscillation f l ≤ ediam (range f) :=
  iInf_le_of_le (range f) (by simp)

/-- The oscillation of `f : E → F` at `x`. -/
noncomputable abbrev oscillationAt [TopologicalSpace E] (f : E → F) (x : E) : ENNReal :=
  oscillation f (𝓝 x)

/-- The oscillation of `f : E → F` within `D` at `x`. -/
noncomputable abbrev oscillationWithinAt [TopologicalSpace E] (f : E → F) (D : Set E) (x : E) :
    ENNReal :=
  oscillation f (𝓝[D] x)

/-- The oscillation of `f` at `x` within a neighborhood `D` of `x` is equal to `oscillation f x` -/
theorem oscillationWithinAt_nhds_eq_oscillationAt [TopologicalSpace E] (f : E → F) (D : Set E)
    (x : E) (hD : D ∈ 𝓝 x) : oscillationWithinAt f D x = oscillationAt f x := by
  rw [oscillationAt, oscillationWithinAt, nhdsWithin_eq_nhds.2 hD]

/-- The oscillation of `f` at `x` within `univ` is equal to `oscillation f x` -/
theorem oscillationWithinAt_univ_eq_oscillationAt [TopologicalSpace E] (f : E → F) (x : E) :
    oscillationWithinAt f univ x = oscillationAt f x :=
  oscillationWithinAt_nhds_eq_oscillationAt f univ x Filter.univ_mem

namespace ContinuousWithinAt

theorem oscillationWithinAt_eq_zero [TopologicalSpace E] {f : E → F} {D : Set E}
    {x : E} (hf : ContinuousWithinAt f D x) : oscillationWithinAt f D x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  have : eball (f x) (ε / 2) ∈ (𝓝[D] x).map f :=
    hf <| eball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le ediam this).trans (le_of_le_of_eq ediam_eball_le ?_)
  exact (ENNReal.mul_div_cancel (by simp) (by simp))

end ContinuousWithinAt

namespace ContinuousAt

theorem oscillationAt_eq_zero [TopologicalSpace E] {f : E → F} {x : E} (hf : ContinuousAt f x) :
    oscillationAt f x = 0 := by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithinAt_univ_eq_oscillationAt f x ▸ hf.oscillationWithinAt_eq_zero

end ContinuousAt

namespace OscillationWithinAt

/-- The oscillation within `D` of `f` at `x ∈ D` is 0 if and only if `ContinuousWithinAt f D x`. -/
theorem eq_zero_iff_continuousWithinAt [TopologicalSpace E] (f : E → F) {D : Set E}
    {x : E} (xD : x ∈ D) : oscillationWithinAt f D x = 0 ↔ ContinuousWithinAt f D x := by
  refine ⟨fun hf ↦ EMetric.tendsto_nhds.mpr (fun ε ε0 ↦ ?_),
    fun hf ↦ hf.oscillationWithinAt_eq_zero⟩
  simp_rw [← hf, oscillationWithinAt, oscillation, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy ↦ lt_of_le_of_lt ?_ Sε)
  exact edist_le_ediam_of_mem (mem_preimage.1 hy) <| mem_preimage.1 (mem_of_mem_nhdsWithin xD hS)

end OscillationWithinAt

namespace OscillationAt

/-- The oscillation of `f` at `x` is 0 if and only if `f` is continuous at `x`. -/
theorem eq_zero_iff_continuousAt [TopologicalSpace E] (f : E → F) (x : E) :
    oscillationAt f x = 0 ↔ ContinuousAt f x := by
  rw [← oscillationWithinAt_univ_eq_oscillationAt, ← continuousWithinAt_univ f x]
  exact OscillationWithinAt.eq_zero_iff_continuousWithinAt f (mem_univ x)

end OscillationAt

namespace IsCompact

variable [PseudoEMetricSpace E] {K : Set E}
variable {f : E → F} {D : Set E} {ε : ENNReal}

/-- If `oscillationWithin f D x < ε` at every `x` in a compact set `K`, then there exists `δ > 0`
such that the oscillation of `f` on `ball x δ ∩ D` is less than `ε` for every `x` in `K`. -/
theorem uniform_oscillationWithinAt (comp : IsCompact K)
    (hK : ∀ x ∈ K, oscillationWithinAt f D x < ε) :
    ∃ δ > 0, ∀ x ∈ K, ediam (f '' (eball x (ENNReal.ofReal δ) ∩ D)) ≤ ε := by
  let S := fun r ↦
    {x : E | ∃ (a : ℝ), (a > r ∧ ediam (f '' (eball x (ENNReal.ofReal a) ∩ D)) ≤ ε)}
  have S_open : ∀ r > 0, IsOpen (S r) := by
    refine fun r _ ↦ EMetric.isOpen_iff.mpr fun x ⟨a, ar, ha⟩ ↦
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refine fun y hy ↦ ⟨a - (a - r) / 2, by linarith,
      le_trans (ediam_mono (image_mono fun z hz ↦ ?_)) ha⟩
    refine ⟨lt_of_le_of_lt (edist_triangle z y x) (lt_of_lt_of_eq (ENNReal.add_lt_add hz.1 hy) ?_),
      hz.2⟩
    rw [← ofReal_add (by linarith) (by linarith), sub_add_cancel]
  have S_cover : K ⊆ ⋃ r > 0, S r := by
    intro x hx
    have : oscillationWithinAt f D x < ε := hK x hx
    simp only [oscillationWithinAt, oscillation, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := EMetric.mem_nhdsWithin_iff.1 hn₁
    simp only [gt_iff_lt, mem_iUnion, exists_prop]
    have : ∀ r', (ENNReal.ofReal r') ≤ r →
        ediam (f '' (eball x (ENNReal.ofReal r') ∩ D)) ≤ ε := by
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
    {f : E → F} {ε : ENNReal} (hK : ∀ x ∈ K, oscillationAt f x < ε) :
    ∃ δ > 0, ∀ x ∈ K, ediam (f '' (eball x (ENNReal.ofReal δ))) ≤ ε := by
  simp only [← oscillationWithinAt_univ_eq_oscillationAt] at hK
  convert! ← comp.uniform_oscillationWithinAt hK
  exact inter_univ _

end IsCompact

section MoveMe

variable {ι : Sort*} {κ : ι → Sort*} {α : Type*} {f : (i : ι) → κ i → α}

@[to_dual iInf₂_le_iff]
theorem le_iSup₂_iff [CompleteSemilatticeSup α] {a : α} :
    a ≤ ⨆ (i) (j), f i j ↔ ∀ b, (∀ i j, f i j ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]

@[to_dual iInf₂_lt_iff]
theorem lt_iSup₂_iff [CompleteLinearOrder α] {a : α} :
    a < ⨆ (i) (j), f i j ↔ ∃ i j, a < f i j := by
  have := lt_iSup_iff (f := fun (ij : PSigma κ) ↦ f ij.1 ij.2) (a := a)
  simp_rw [PSigma.exists, iSup_psigma] at this
  exact this

@[to_dual iInf₂_le_iff_forall_lt]
theorem le_iSup₂_iff_forall_lt [CompleteLinearOrder α] {l : α} :
    l ≤ ⨆ (i) (j), f i j ↔ ∀ b < l, ∃ i j, b < f i j := by
  have := le_iSup_iff_forall_lt (f := fun (ij : PSigma κ) ↦ f ij.1 ij.2) (l := l)
  simp_rw [PSigma.exists, iSup_psigma] at this
  exact this

@[to_dual lt_iInf₂_iff]
theorem iSup₂_lt_iff [CompleteLattice α] {l : α} :
    ⨆ (i) (j), f i j < l ↔ ∃ b < l, ∀ i j, f i j ≤ b := by
  have := iSup_lt_iff (f := fun (ij : PSigma κ) ↦ f ij.1 ij.2) (l := l)
  simp_rw [PSigma.forall, iSup_psigma] at this
  exact this

lemma mul_biInf {p : ι → Prop} (hp : ∃ i, p i) {a : ℝ≥0∞} {f : ι → ℝ≥0∞}
    (hinfty : a = ∞ → ⨅ (i) (_ : p i), f i = 0 → ∃ i, ∃ (_ : p i), f i = 0) :
    a * ⨅ (i) (_ : p i), f i = ⨅ (i) (_ : p i), a * f i := by
  haveI : Nonempty {i // p i} := nonempty_subtype.mpr hp
  have := mul_iInf (ι := {i // p i}) (a := a) (f := (f ·))
  simp_rw [iInf_subtype, Subtype.exists] at this
  exact this hinfty

@[to_dual iInf₂_eq_of_forall_ge_of_forall_gt_exists_lt]
theorem iSup₂_eq_of_forall_le_of_forall_lt_exists_gt [CompleteLattice α] {b : α}
    (h₁ : ∀ i j, f i j ≤ b) (h₂ : ∀ w, w < b → ∃ i j, w < f i j) : ⨆ (i) (j), f i j = b := by
  have := iSup_eq_of_forall_le_of_forall_lt_exists_gt
    (f := fun (ij : PSigma κ) ↦ f ij.1 ij.2) (b := b)
  simp_rw [PSigma.forall, PSigma.exists, iSup_psigma] at this
  exact this h₁ h₂

end MoveMe

section Cauchy

variable {f : E → F}

theorem EMetric.cauchy_iff_iInf_ediam_eq_zero (l : Filter F) [NeBot l] :
    Cauchy l ↔ ⨅ s ∈ l, ediam s = 0 := by
  rw [EMetric.cauchy_iff, ←nonpos_iff_eq_zero, iInf₂_le_iff_forall_lt]
  constructor
  · intro h ε hε
    rcases exists_between hε with ⟨η, hη⟩
    rcases h.right η hη.1 with ⟨s, hs₁, hs₂⟩
    use s, hs₁
    apply iSup₂_lt_iff.mpr
    use η, hη.2
    intro i hi
    apply iSup₂_le_iff.mpr
    intro j hj
    exact hs₂ i hi j hj |>.le
  · intro h
    use NeBot.ne'
    intro ε hε
    rcases h ε hε with ⟨s, hs₁, hs₂⟩
    use s, hs₁
    intro i hi j hj
    rcases iSup₂_lt_iff.mp hs₂ with ⟨l, hl, hs₃⟩
    specialize hs₃ i hi
    exact iSup₂_le_iff.mp hs₃ j hj |>.trans_lt hl

theorem cauchy_iff_oscillation_eq_zero (l : Filter E) [NeBot l] :
    Cauchy (l.map f) ↔ oscillation f l = 0 :=
  EMetric.cauchy_iff_iInf_ediam_eq_zero _

/-- A function `f` whose domain is a complete `EMetric` space converges to a point along a filter if
and only if its oscillation along `l` is equal to zero. -/
theorem EMetric.tendsTo_nhds_iff_oscillation_eq_zero [CompleteSpace F] (l : Filter E) [NeBot l] :
    (∃ x, Tendsto f l (𝓝 x)) ↔ oscillation f l = 0 := by
  rw [←cauchy_map_iff_exists_tendsto]
  exact cauchy_iff_oscillation_eq_zero _

end Cauchy

section Lipschitz

variable {α β γ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

theorem LipschitzWith.oscillation_comp₂_le (g : α → β → γ) (f₁ : E → α) (f₂ : E → β)
    {K₁ K₂ : NNReal} (l : Filter E)
    (hf₁ : ∀ b, LipschitzWith K₁ (g · b)) (hf₂ : ∀ a, LipschitzWith K₂ (g a ·)) :
    oscillation (fun a ↦ g (f₁ a) (f₂ a)) l
      ≤ ↑K₁ * oscillation f₁ l + ↑K₂ * oscillation f₂ l := by
  unfold oscillation
  simp_rw [mul_biInf ⟨_, Filter.univ_mem⟩ (coe_ne_top · |>.elim)]
  setm _ ≤ ?a + ?b
  by_cases! ha : a = ∞; · simp [ha]
  by_cases! hb : b = ∞; · simp [hb]
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  rcases iInf₂_le_iff_forall_lt (l := a) |>.mp le_rfl (a + ε / 2)
    (lt_add_right ha (by norm_num [hε.ne'])) with ⟨sa, hsa, hsa'⟩
  rcases iInf₂_le_iff_forall_lt (l := b) |>.mp le_rfl (b + ε / 2)
    (lt_add_right hb (by norm_num [hε.ne'])) with ⟨sb, hsb, hsb'⟩
  rw [show a + b + ε = a + ε / 2 + (b + ε / 2) by
    ring_nf
    rw [ENNReal.div_mul_cancel (by positivity) (by finiteness)]]
  apply ENNReal.add_lt_add hsa' hsb' |>.trans_le' _ |>.le
  apply iInf₂_le_of_le (image2 g sa sb) _ _
  · rw [mem_map] at ⊢ hsa hsb
    exact l.mem_of_superset (l.inter_mem hsa hsb) fun a ⟨h₁, h₂⟩ ↦ ⟨f₁ a, h₁, f₂ a, h₂, rfl⟩
  · exact LipschitzOnWith.ediam_image2_le _ _ _
      (fun s _ ↦ hf₁ s |>.lipschitzOnWith)
      (fun s _ ↦ hf₂ s |>.lipschitzOnWith)

end Lipschitz

section SeminormedAddCommGroup

variable {F : Type*} [SeminormedCommGroup F]

@[to_additive]
theorem oscillation_mul_le (f₁ : E → F) (f₂ : E → F) (l : Filter E) :
    oscillation (f₁ * f₂) l ≤ oscillation f₁ l + oscillation f₂ l :=
  LipschitzWith.oscillation_comp₂_le (· * ·) f₁ f₂ l
    (fun _ => (isometry_mul_right _).lipschitz)
    (fun _ => (isometry_mul_left _).lipschitz)
    |>.trans_eq (by simp only [coe_one, one_mul])

@[to_additive]
theorem oscillation_le_add_div (f₁ : E → F) (f₂ : E → F) (l : Filter E) :
    oscillation f₁ l ≤ oscillation f₂ l + oscillation (f₁ / f₂) l := by
  nth_rw 1 [show f₁ = f₂ * (f₁ / f₂) by simp]
  exact oscillation_mul_le ..

@[to_additive oscillation_le_two_mul_iSup_enorm]
theorem oscillation_le_two_mul_iSup_enorm' (f : E → F) (l : Filter E) :
    oscillation f l ≤ 2 * iSup (‖f ·‖ₑ) := by
  apply oscillation_le_ediam_range.trans
  refine ediam_le fun x hx y hy => ?_
  rw [edist_eq_enorm_div x y, two_mul]
  apply enorm_div_le.trans <| add_le_add _ _
  · exact hx.out.elim fun z hz ↦ hz ▸ le_iSup (‖f ·‖ₑ) ..
  · exact hy.out.elim fun z hz ↦ hz ▸ le_iSup (‖f ·‖ₑ) ..

end SeminormedAddCommGroup
