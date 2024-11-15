/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.UniformGroup.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a linearly ordered commutative group `G` with the order
topology which is also order closed. Therefore it applies also when the codomain is `ℤ`, `ℚ`, or
`ℝ≥0ˣ`.
-/

open Filter Topology

variable {ι α G : Type*} [SemilatticeSup ι]
    [Nonempty ι] [TopologicalSpace α] [LinearOrderedCommGroup G] [UniformSpace G]
    [UniformGroup G] [OrderTopology G] [OrderClosedTopology G] [Nontrivial G]

namespace UniformGroup

variable {F : ι → α → G} {f : α → G}

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact space converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive "**Dini's theorem** If `F n` is a monotone increasing collection of continuous
functions on a compact space converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop := by
  have F_le_f (x : α) (n : ι) : F n x ≤ f x :=
    (monotone_app _ _ hF_mono).ge_of_tendsto (h_tendsto x) n
  rw [tendstoUniformly_iff F f atTop]
  intro v hv
  simp_rw +singlePass [← tendsto_div_nhds_one_iff] at h_tendsto
  obtain ⟨y, hy⟩ := exists_one_lt' (α := G)
  obtain ⟨l, u, h₀, h⟩ := mem_nhds_iff_exists_Ioo_subset' ⟨y⁻¹, inv_lt_one'.mpr hy⟩ ⟨y, hy⟩ |>.mp hv
  have mono_preimage_Ioo : Monotone (fun i => (fun x => F i x / f x) ⁻¹' Set.Ioo l u) := by
    intro n m hnm x hx
    simp only [Set.mem_preimage, Set.mem_Ioo] at hx ⊢
    refine ⟨hx.1.trans_le ?_, div_le_one'.2 (F_le_f _ _) |>.trans_lt h₀.2⟩
    gcongr
    exact hF_mono hnm x
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover _
    (fun n ↦ isOpen_Ioo.preimage <| (hF_cont n).div' hf)
    (fun x ↦ by simpa using Eventually.exists <| (h_tendsto x).eventually <| isOpen_Ioo.mem_nhds h₀)
    (directed_of_isDirected_le mono_preimage_Ioo)
  filter_upwards [Ici_mem_atTop n] with m (hnm : n ≤ m) x
  exact h <| mono_preimage_Ioo hnm <| hn trivial

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive "**Dini's theorem** If `F n` is a monotone increasing collection of continuous
functions on a compact set `s` converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have := isCompact_iff_compactSpace.mp hs
  exact tendstoUniformly_of_forall_tendsto (hF_cont · |>.restrict) (fun _ _ h x ↦ hF_mono _ x.2 h)
    hf.restrict (fun x ↦ h_tendsto x x.2)

end UniformGroup

namespace ContinuousMap

variable {F : ι → C(α, G)} {f : C(α, G)}

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on
converging pointwise to a continuous `f`, then `F n` converges to `f` in the
compact-open topology.

This version requires the codomain to be an `AddGroup` instead of a `Group`.
-/
@[to_additive tendsto_of_pointwise "**Dini's theorem** If `F n` is a monotone increasing collection
of continuous functions on converging pointwise to a continuous `f`, then `F n` converges to `f` in
the compact-open topology."]
lemma tendsto_of_pointwise' (hF_mono : Monotone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_iff_forall_compact_tendstoUniformlyOn.mpr fun _ h_cpct ↦
    UniformGroup.tendstoUniformlyOn_of_forall_tendsto h_cpct
      (F · |>.continuous.continuousOn) (fun x _ _ _ h ↦ hF_mono h x)
      f.continuous.continuousOn (fun x _ ↦ h_tendsto x)

end ContinuousMap
