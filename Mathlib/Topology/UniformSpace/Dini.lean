/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a normed lattice additive commutative group `G`.
This theorem is true in a different generality as well: when `G` is a linearly ordered topological
group with the order topology. This weakens the norm assumption, in exchange for strengthening to
a linear order. This separate generality is not included in this file, but that generality was
included in initial drafts of the original
https://github.com/leanprover-community/mathlib4/pull/19068 and can be recovered if
necessary.

The key idea of the proof is to use a particular basis of `𝓝 0` which consists of open sets that
are somehow monotone in the sense that if `s` is in the basis, and `0 ≤ x ≤ y`, then
`y ∈ s → x ∈ s`, and so the proof would work on any topological ordered group possessing
such a basis. In the case of a linearly ordered topological group with the order topology, this
basis is `nhds_basis_Ioo`. In the case of a normed lattice additive commutative group, this basis
is `nhds_basis_ball`, and the fact that this basis satisfies the monotonicity criterion
corresponds to `HasSolidNorm`.
-/

public section

open Filter Topology

variable {ι α G : Type*} [Preorder ι] [TopologicalSpace α]
  [NormedAddCommGroup G] [Lattice G] [HasSolidNorm G] [IsOrderedAddMonoid G]

section Unbundled

open Metric

variable {F : ι → α → G} {f : α → G}

namespace Monotone

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := by
  refine (atTop : Filter ι).eq_or_neBot.elim (fun h ↦ ?eq_bot) (fun _ ↦ ?_)
  case eq_bot => simp [h, tendstoLocallyUniformly_iff_forall_tendsto]
  have F_le_f (x : α) (n : ι) : F n x ≤ f x := by
    refine ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
    exact hF_mono hnm x
  simp_rw [Metric.tendstoLocallyUniformly_iff, dist_eq_norm']
  intro ε ε_pos x
  specialize h_tendsto x
  rw [tendsto_iff_norm_sub_tendsto_zero] at h_tendsto
  obtain ⟨n, hn⟩ := h_tendsto.eventually (eventually_lt_nhds ε_pos) |>.exists
  refine ⟨{y | ‖F n y - f y‖ < ε}, ⟨isOpen_lt (by fun_prop) continuous_const |>.mem_nhds hn, ?_⟩⟩
  filter_upwards [eventually_ge_atTop n] with m hnm z hz
  refine norm_le_norm_of_abs_le_abs ?_ |>.trans_lt hz
  simp only [abs_of_nonpos (sub_nonpos_of_le (F_le_f _ _)), neg_sub, sub_le_sub_iff_left]
  exact hF_mono hnm z

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges locally uniformly
to `f`. -/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact tendstoLocallyUniformly_of_forall_tendsto (hF_cont · |>.restrict)
    (fun _ _ h x ↦ hF_mono _ x.2 h) hf.restrict (fun x ↦ h_tendsto x x.2)

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
compact space converging pointwise to a continuous function `f`, then `F n` converges uniformly to
`f`. -/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp <|
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous function `f`, then `F n` converges uniformly
to `f`. -/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs |>.mp <|
    tendstoLocallyUniformlyOn_of_forall_tendsto hF_cont hF_mono hf h_tendsto

end Monotone

namespace Antitone

set_option backward.isDefEq.respectTransparency false in
/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : ∀ i, Continuous (F i)) (hF_anti : Antitone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop :=
  Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

set_option backward.isDefEq.respectTransparency false in
/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
set `s` converging pointwise to a continuous function `f`, then `F n` converges locally uniformly
to `f`. -/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_anti : ∀ x ∈ s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s :=
  Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

set_option backward.isDefEq.respectTransparency false in
/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
compact space converging pointwise to a continuous function `f`, then `F n` converges uniformly
to `f`. -/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

set_option backward.isDefEq.respectTransparency false in
/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions on a
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

/-- **Dini's theorem**: if `F n` is a monotone increasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges to `f` in the
compact-open topology. -/
lemma tendsto_of_monotone_of_pointwise (hF_mono : Monotone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_tendstoLocallyUniformly <|
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

set_option backward.isDefEq.respectTransparency false in
/-- **Dini's theorem**: if `F n` is a monotone decreasing collection of continuous functions
converging pointwise to a continuous function `f`, then `F n` converges to `f` in the
compact-open topology. -/
lemma tendsto_of_antitone_of_pointwise (hF_anti : Antitone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

end ContinuousMap
