/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a normed latttice additive commutative group `G`. -/

open Filter Topology

variable {ι α G : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable [TopologicalSpace α] [NormedLatticeAddCommGroup G]

section Unbundled

open TopologicalAddGroup Metric

variable {F : ι → α → G} {f : α → G}

namespace Monotone

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := by
  refine subsingleton_or_nontrivial G |>.elim (fun _ ↦ ?subsingleton) (fun _ ↦ ?_)
  case subsingleton =>
    rw [funext fun x => Subsingleton.elim (F x) f, TendstoLocallyUniformly]
    -- missing `tendstoLocallyUniformly_const`
    exact fun _ h x ↦ ⟨Set.univ, univ_mem, .of_forall fun _ _ _ ↦ mem_uniformity_of_eq h rfl⟩
  have F_le_f (x : α) (n : ι) : F n x ≤ f x := by
    refine _root_.ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
    exact hF_mono hnm x
  rw [tendstoLocallyUniformly_iff F f atTop UniformAddGroup.toUniformSpace_eq]
  intro v hv x
  obtain ⟨ε, ε_pos, hε⟩ := Metric.nhds_basis_ball.mem_iff.mp hv
  simp_rw +singlePass [← tendsto_sub_nhds_zero_iff] at h_tendsto
  obtain ⟨n, hn⟩ := h_tendsto x |>.basis_right nhds_basis_ball ε ε_pos |>.exists
  refine ⟨_, (hF_cont n).sub hf |>.continuousAt.preimage_mem_nhds <| isOpen_ball.mem_nhds hn, ?_⟩
  have mono_preimage_Ioo : Monotone (fun i => (F i - f) ⁻¹' Metric.ball 0 ε) := by
    intro n m hnm x hx
    simp only [Set.mem_preimage, Pi.sub_apply, mem_ball, dist_zero_right] at hx ⊢
    refine norm_le_norm_of_abs_le_abs ?_ |>.trans_lt hx
    simp only [abs_of_nonpos (sub_nonpos.mpr (F_le_f _ _)), neg_sub]
    gcongr
    exact hF_mono hnm x
  filter_upwards [Ici_mem_atTop n] with m (hnm : n ≤ m) z hz
  exact hε <| mono_preimage_Ioo hnm hz

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact space converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp <|
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have := isCompact_iff_compactSpace.mp hs
  exact tendstoUniformly_of_forall_tendsto (hF_cont · |>.restrict) (fun _ _ h x ↦ hF_mono _ x.2 h)
    hf.restrict (fun x ↦ h_tendsto x x.2)

end Monotone

namespace Antitone

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_anti : Antitone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop :=
  Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
compact space converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_anti : ∀ x ∈ s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto

end Antitone

end Unbundled

namespace ContinuousMap

variable {F : ι → C(α, G)} {f : C(α, G)}

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on
converging pointwise to a continuous `f`, then `F n` converges to `f` in the
compact-open topology. -/
lemma tendsto_of_monotone_of_pointwise (hF_mono : Monotone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_tendstoLocallyUniformly <|
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on
converging pointwise to a continuous `f`, then `F n` converges to `f` in the
compact-open topology. -/
lemma tendsto_of_antitone_of_pointwise (hF_anti : Antitone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

end ContinuousMap
