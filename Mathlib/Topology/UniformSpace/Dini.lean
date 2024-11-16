/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Topology.Algebra.UniformGroup.Basic
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a linearly ordered commutative group `G` with the order
topology which is also order closed. Therefore it applies also when the codomain is `ℤ`, `ℚ`, or
`ℝ≥0ˣ`.
-/

open Filter Topology

variable {ι α G : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [TopologicalSpace α] [LinearOrderedCommGroup G]

section Unbundled

open TopologicalGroup

variable [u : UniformSpace G] [TopologicalGroup G] [OrderTopology G]
variable {F : ι → α → G} {f : α → G}

namespace Monotone

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
@[to_additive tendstoLocallyUniformly_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone increasing collection of continuous
functions on a converging pointwise to a continuous function `f`, then `F n` converges locally
uniformly to `f`."]
lemma tendstoLocallyUniformly_of_forall_tendsto'
    (hF_cont : ∀ i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
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
  rw [tendstoLocallyUniformly_iff F f atTop hu]
  intro v hv x
  simp_rw +singlePass [← tendsto_div_nhds_one_iff] at h_tendsto
  obtain ⟨y, hy⟩ := exists_one_lt' (α := G)
  obtain ⟨l, u, h₀, h⟩ := mem_nhds_iff_exists_Ioo_subset' ⟨y⁻¹, inv_lt_one'.mpr hy⟩ ⟨y, hy⟩ |>.mp hv
  obtain ⟨n, (hn : (F n / f) x ∈ Set.Ioo l u)⟩ :=
    Eventually.exists <| (h_tendsto x).eventually <| isOpen_Ioo.mem_nhds h₀
  refine ⟨(F n / f) ⁻¹' Set.Ioo l u, (isOpen_Ioo.preimage <| (hF_cont n).div' hf).mem_nhds hn, ?_⟩
  have mono_preimage_Ioo : Monotone (fun i => (F i / f) ⁻¹' Set.Ioo l u) := by
    intro n m hnm x hx
    simp only [Set.mem_preimage, Set.mem_Ioo] at hx ⊢
    refine ⟨hx.1.trans_le ?_, div_le_one'.2 (F_le_f _ _) |>.trans_lt h₀.2⟩
    simpa only [Pi.div_apply, div_le_iff_le_mul, div_mul_cancel] using hF_mono hnm x
  filter_upwards [Ici_mem_atTop n] with m (hnm : n ≤ m) z hz
  exact h <| mono_preimage_Ioo hnm hz

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact space converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive tendstoUniformly_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone increasing collection of continuous
functions on a compact space converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformly_of_forall_tendsto' [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
    TendstoUniformly F f atTop :=
  tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp <|
    tendstoLocallyUniformly_of_forall_tendsto' hF_cont hF_mono hf h_tendsto hu

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive tendstoUniformlyOn_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone increasing collection of continuous
functions on a compact set `s` converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformlyOn_of_forall_tendsto' {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_mono : ∀ x ∈ s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
    TendstoUniformlyOn F f atTop s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have := isCompact_iff_compactSpace.mp hs
  exact tendstoUniformly_of_forall_tendsto' (hF_cont · |>.restrict) (fun _ _ h x ↦ hF_mono _ x.2 h)
    hf.restrict (fun x ↦ h_tendsto x x.2) hu

end Monotone
namespace Antitone

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
converging pointwise to a continuous function `f`, then `F n` converges locally uniformly to `f`. -/
@[to_additive tendstoLocallyUniformly_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone decreasing collection of continuous
functions on a converging pointwise to a continuous function `f`, then `F n` converges locally
uniformly to `f`."]
lemma tendstoLocallyUniformly_of_forall_tendsto'
    (hF_cont : ∀ i, Continuous (F i)) (hF_anti : Antitone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
    TendstoLocallyUniformly F f atTop :=
  Monotone.tendstoLocallyUniformly_of_forall_tendsto' (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto hu

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
compact space converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive tendstoUniformly_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone decreasing collection of continuous
functions on a compact space converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformly_of_forall_tendsto' [CompactSpace α] (hF_cont : ∀ i, Continuous (F i))
    (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto' (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto hu

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on a
compact set `s` converging pointwise to a continuous `f`, then `F n` converges uniformly to `f`. -/
@[to_additive tendstoUniformlyOn_of_forall_tendsto
"**Dini's theorem** If `F n` is a monotone decreasing collection of continuous
functions on a compact set `s` converging pointwise to a continuous `f`, then `F n` converges
uniformly to `f`."]
lemma tendstoUniformlyOn_of_forall_tendsto' {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ i, ContinuousOn (F i) s) (hF_anti : ∀ x ∈ s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : ∀ x ∈ s, Tendsto (F · x) atTop (𝓝 (f x)))
    (hu : toUniformSpace G = u := by first | exact UniformGroup.toUniformSpace_eq G | rfl) :
    TendstoUniformlyOn F f atTop s :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto' (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto hu

end Antitone

end Unbundled

namespace ContinuousMap

variable [TopologicalSpace G] [TopologicalGroup G] [OrderTopology G]
variable {F : ι → C(α, G)} {f : C(α, G)}

/-- **Dini's theorem** If `F n` is a monotone increasing collection of continuous functions on
converging pointwise to a continuous `f`, then `F n` converges to `f` in the
compact-open topology.

This version requires the codomain to be an `AddGroup` instead of a `Group`.
-/
@[to_additive tendsto_of_monotone_of_pointwise
"**Dini's theorem** If `F n` is a monotone increasing collection
of continuous functions on converging pointwise to a continuous `f`, then `F n` converges to `f` in
the compact-open topology."]
lemma tendsto_of_monotone_of_pointwise' (hF_mono : Monotone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  let _ := TopologicalGroup.toUniformSpace G
  tendsto_of_tendstoLocallyUniformly <|
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto' (F · |>.continuous) f.continuous h_tendsto

/-- **Dini's theorem** If `F n` is a monotone decreasing collection of continuous functions on
converging pointwise to a continuous `f`, then `F n` converges to `f` in the
compact-open topology.

This version requires the codomain to be an `AddGroup` instead of a `Group`.
-/
@[to_additive tendsto_of_antitone_of_pointwise
"**Dini's theorem** If `F n` is a monotone decreasing collection
of continuous functions on converging pointwise to a continuous `f`, then `F n` converges to `f` in
the compact-open topology."]
lemma tendsto_of_antitone_of_pointwise' (hF_anti : Antitone F)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_monotone_of_pointwise' (G := Gᵒᵈ) hF_anti h_tendsto

end ContinuousMap
