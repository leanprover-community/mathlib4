/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Algebra.Group.AddTorsor
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.Basic
import Batteries.Tactic.Congr
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.NAry
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Map
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Neighborhoods

/-!
# Asymptotic cone of a set

This file defines the asymptotic cone of a set in a topological affine space.

## Implementation details

The asymptotic cone of a set $A$ is usually defined as the set of points $v$ for which there exist
sequences $t_n > 0$ and $x_n \in A$ such that $t_n \to 0$ and $t_n x_n \to v$. We take a different
approach here using filters: we define the asymptotic cone of `s` as the set of vectors `v` such
that `∃ᶠ p in Filter.atTop • 𝓝 v, p ∈ s` holds.

## Main definitions

* `AffineSpace.asymptoticNhds`: the filter of neighborhoods at infinity in some direction.
* `asymptoticCone`: the asymptotic cone of a subset of a topological affine space.

## Main statements

* `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  closed convex set `s`, then every ray of direction `v` starting from `s` is contained in `s`.
* `Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  convex set `s`, then every ray of direction `v` starting from the interior of `s` is contained in
  `s`.
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

section General

variable
  {k V P : Type*}
  [Field k] [LinearOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace V]

namespace AffineSpace

variable (k P) in
/-- In a topological affine space `P` over `k`, `AffineSpace.asymptoticNhds k P v` is the filter of
neighborhoods at infinity in directions near `v`. In a topological vector space, this is the filter
`Filter.atTop • 𝓝 v`. To support affine spaces, the actual definition is different and should be
considered an implementation detail. Use `AffineSpace.asymptoticNhds_eq_smul` or
`AffineSpace.asymptoticNhds_eq_smul_vadd` for unfolding. -/
@[irreducible]
def asymptoticNhds (v : V) : Filter P := ⨆ p, atTop (α := k) • 𝓝 v +ᵥ pure p

theorem asymptoticNhds_vadd_pure (v : V) (p : P) :
    asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v := by
  simp_rw [asymptoticNhds, vadd_pure, map_iSup, map_map, Function.comp_def]
  refine (Equiv.vaddConst p).iSup_congr fun _ => ?_
  simp [add_vadd]

theorem vadd_asymptoticNhds (u v : V) : u +ᵥ asymptoticNhds k P v = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← asymptoticNhds_vadd_pure v p]
  simp_rw [← asymptoticNhds_vadd_pure v (u +ᵥ p), vadd_pure, ← Filter.map_vadd, map_map]
  congr with v
  exact vadd_comm u v p

variable {α : Type*} {l : Filter α}

theorem _root_.Filter.Tendsto.asymptoticNhds_vadd_const {f : α → V} {v : V} (p : P)
    (hf : Tendsto f l (asymptoticNhds k V v)) :
    Tendsto (fun x => f x +ᵥ p) l (asymptoticNhds k P v) := by
  rw [← asymptoticNhds_vadd_pure, vadd_pure]
  exact tendsto_map.comp hf

theorem _root_.Filter.Tendsto.const_vadd_asymptoticNhds {f : α → P} {v : V} (u : V)
    (hf : Tendsto f l (asymptoticNhds k P v)) :
    Tendsto (fun x => u +ᵥ f x) l (asymptoticNhds k P v) := by
  rw [← vadd_asymptoticNhds u, ← Filter.map_vadd]
  exact tendsto_map.comp hf

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]

theorem asymptoticNhds_eq_smul (v : V) : asymptoticNhds k V v = atTop (α := k) • 𝓝 v := by
  unfold asymptoticNhds
  apply le_antisymm
  · refine iSup_le fun u => ?_
    simp_rw [vadd_eq_add, add_pure, ← map₂_smul, map_map₂, ← map_prod_eq_map₂]
    have : (fun x : k × V => x.1 • x.2 + u) =ᶠ[atTop ×ˢ 𝓝 v]
        (Function.uncurry (· • ·)) ∘ (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) := by
      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
      simp [h]
    rw [map_congr this, ← map_map]
    apply map_mono
    have : Tendsto (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) (atTop ×ˢ 𝓝 v) _ :=
      tendsto_fst.prodMk <| tendsto_snd.add <| tendsto_fst.inv_tendsto_atTop.smul_const u
    simpa
  · apply (le_iSup _ 0).trans'
    simp

theorem asymptoticNhds_eq_smul_vadd (v : V) (p : P) :
    asymptoticNhds k P v = atTop (α := k) • 𝓝 v +ᵥ pure p := by
  rw [← asymptoticNhds_eq_smul, asymptoticNhds_vadd_pure]

instance {v : V} : (asymptoticNhds k P v).NeBot := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd v p]
  infer_instance

private theorem asymptoticNhds_zero' : asymptoticNhds k V (0 : V) = ⊤ := by
  rw [← top_le_iff, ← iSup_pure_eq_top, iSup_le_iff]
  intro v
  rw [← map_const (f := atTop (α := k))]
  have : (fun _ => v) =ᶠ[atTop (α := k)]
      (Function.uncurry (· • ·)) ∘ (fun c => (c, c⁻¹ • v)) := by
    filter_upwards [eventually_ne_atTop 0] with _ h
    simp [h]
  rw [map_congr this, ← map_map, asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂]
  apply map_mono
  have : Tendsto (fun c => (c, c⁻¹ • v)) (atTop (α := k)) _ :=
    tendsto_id.prodMk <| tendsto_inv_atTop_zero.smul_const v
  simpa

@[simp]
theorem asymptoticNhds_zero : asymptoticNhds k P (0 : V) = ⊤ := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← asymptoticNhds_vadd_pure 0 p, asymptoticNhds_zero', vadd_pure]
  exact (Equiv.vaddConst p).surjective.filter_map_top

theorem _root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds {f : α → k} {g : α → V} {v : V}
    (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 v)) :
    Tendsto (fun x => f x • g x) l (asymptoticNhds k V v) := by
  rw [asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂]
  exact tendsto_map.comp (hf.prodMk hg)

theorem _root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds {f : α → k} (v : V)
    (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • v) l (asymptoticNhds k V v) :=
  hf.atTop_smul_nhds_tendsto_asymptoticNhds tendsto_const_nhds

theorem asymptoticNhds_smul (v : V) {c : k} (hc : 0 < c) :
    asymptoticNhds k P (c • v) = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [asymptoticNhds_eq_smul_vadd _ p,
    ← show map (c • ·) (𝓝 v) = 𝓝 (c • v) from
      (Homeomorph.smulOfNeZero c hc.ne').map_nhds_eq v,
    ← map₂_smul, map₂_map_right, smul_smul, ← map₂_map_left,
    show map (· * c) atTop = atTop from (OrderIso.mulRight₀ _ hc).map_atTop]

@[simp]
theorem nhds_bind_asymptoticNhds (v : V) :
    (𝓝 v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  apply le_antisymm
  · have ⟨p⟩ : Nonempty P := inferInstance
    eta_expand
    simp_rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure]
    nth_rw 2 [← nhds_bind_nhds]
    simp only [le_def, mem_map, ← map₂_smul, mem_map₂_iff, mem_bind]
    grind
  · rw [← pure_bind v (asymptoticNhds k P)]
    exact bind_mono (pure_le_nhds v) .rfl

@[simp]
theorem asymptoticNhds_bind_nhds [TopologicalSpace P] [IsTopologicalAddTorsor P] (v : V) :
    (asymptoticNhds k P v).bind 𝓝 = asymptoticNhds k P v := by
  refine le_antisymm (fun s h => ?_) (bind_mono le_rfl (.of_forall pure_le_nhds))
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at h ⊢
  rw [← nhds_bind_nhds] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hs⟩ := h
  rw [mem_bind] at ht₂
  obtain ⟨t₃, ht₃, ht₂⟩ := ht₂
  rw [bind_map, mem_bind]
  refine ⟨(t₁ ∩ Set.Ioi 0) • t₃, smul_mem_smul (inter_mem ht₁ (Ioi_mem_atTop _)) ht₃,
    Set.forall_mem_image2.mpr fun c ⟨hc₁, hc₂⟩ u hu => ?_⟩
  rw [show s = (· -ᵥ p) ⁻¹' ((· +ᵥ p) ⁻¹' s) by simp [Set.preimage_preimage]]
  apply tendsto_id.vsub tendsto_const_nhds
  rw [vadd_vsub]
  filter_upwards [smul_mem_nhds_smul₀ hc₂.ne' (ht₂ u hu)]
  rw [← Set.image_smul, Set.forall_mem_image]
  exact fun w hw => hs (Set.smul_mem_smul hc₁ hw)

@[simp]
theorem asymptoticNhds_bind_asymptoticNhds (v : V) :
    (asymptoticNhds k V v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  refine Filter.ext' fun p => ?_
  rw [asymptoticNhds_eq_smul, eventually_bind, ← map₂_smul, ← map_prod_eq_map₂, eventually_map,
    ← nhds_bind_asymptoticNhds, eventually_bind]
  nth_rw 2 [← map_snd_prod (atTop (α := k)) (𝓝 v)]
  rw [eventually_map]
  apply eventually_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ (hc : 0 < c)
  simp only [asymptoticNhds_smul _ hc]

end AffineSpace

open AffineSpace

variable (k) in
/-- The set of directions `v` for which the set has points arbitrarily far in directions near `v`.
-/
def asymptoticCone (s : Set P) : Set V := {v | ∃ᶠ p in asymptoticNhds k P v, p ∈ s}

theorem mem_asymptoticCone_iff {v : V} {s : Set P} :
    v ∈ asymptoticCone k s ↔ ∃ᶠ p in asymptoticNhds k P v, p ∈ s :=
  Iff.rfl

@[simp]
theorem asymptoticCone_empty : asymptoticCone k (∅ : Set P) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ => frequently_false _

@[gcongr]
theorem asymptoticCone_mono {s t : Set P} (h : s ⊆ t) : asymptoticCone k s ⊆ asymptoticCone k t :=
  fun _ h' => h'.mono h

theorem asymptoticCone_union {s t : Set P} :
    asymptoticCone k (s ∪ t) = asymptoticCone k s ∪ asymptoticCone k t := by
  ext
  simp only [Set.mem_union, mem_asymptoticCone_iff, Filter.frequently_or_distrib]

theorem asymptoticCone_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set P) :
    asymptoticCone k (⋃ i ∈ s, f i) = ⋃ i ∈ s, asymptoticCone k (f i) := by
  induction s, hs using Set.Finite.induction_on <;>
    simp [asymptoticCone_union, *]

theorem asymptoticCone_sUnion {S : Set (Set P)} (hS : S.Finite) :
    asymptoticCone k (⋃₀ S) = ⋃ s ∈ S, asymptoticCone k s := by
  rw [Set.sUnion_eq_biUnion, asymptoticCone_biUnion hS]

nonrec theorem Finset.asymptoticCone_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set P) :
    asymptoticCone k (⋃ i ∈ s, f i) = ⋃ i ∈ s, asymptoticCone k (f i) :=
  asymptoticCone_biUnion s.finite_toSet f

theorem asymptoticCone_iUnion_of_finite {ι : Type*} [Finite ι] (f : ι → Set P) :
    asymptoticCone k (⋃ i, f i) = ⋃ i, asymptoticCone k (f i) := by
  rw [← Set.sUnion_range, asymptoticCone_sUnion (Set.finite_range f), Set.biUnion_range]

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]

theorem zero_mem_asymptoticCone {s : Set P} : 0 ∈ asymptoticCone k s ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun _ => ?_⟩
  · simp +contextual [Set.not_nonempty_iff_eq_empty]
  · simpa [mem_asymptoticCone_iff]

theorem asymptoticCone_nonempty {s : Set P} : (asymptoticCone k s).Nonempty ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun h => ⟨0, zero_mem_asymptoticCone.mpr h⟩⟩
  simp +contextual [Set.not_nonempty_iff_eq_empty]

@[simp]
theorem smul_mem_asymptoticCone_iff {s : Set P} {c : k} {v : V} (hc : 0 < c) :
    c • v ∈ asymptoticCone k s ↔ v ∈ asymptoticCone k s := by
  simp_rw [mem_asymptoticCone_iff, asymptoticNhds_smul v hc]

theorem smul_mem_asymptoticCone {s : Set P} {c : k} {v : V} (hc : 0 ≤ c)
    (h : v ∈ asymptoticCone k s) : c • v ∈ asymptoticCone k s := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mem_asymptoticCone, ← asymptoticCone_nonempty (k := k)]; exact ⟨v, h⟩
  · rwa [smul_mem_asymptoticCone_iff hc]

theorem asymptoticCone_eq_closure_of_forall_smul_mem {s : Set V}
    (hs : ∀ c : k, 0 < c → ∀ x ∈ s, c • x ∈ s) : asymptoticCone k s = closure s := by
  ext v
  rw [mem_closure_iff_frequently, ← map_snd_prod (atTop (α := k)) (𝓝 v), frequently_map,
    mem_asymptoticCone_iff, asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂, frequently_map]
  apply frequently_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ hc
  refine ⟨fun hu => ?_, hs c hc u⟩
  specialize hs c⁻¹ (inv_pos_of_pos hc) (c • u) hu
  rwa [inv_smul_smul₀ hc.ne'] at hs

theorem asymptoticCone_submodule {s : Submodule k V} : asymptoticCone k (s : Set V) = closure s :=
  asymptoticCone_eq_closure_of_forall_smul_mem fun _ _ _ h => s.smul_mem _ h

theorem asymptoticCone_affineSubspace {s : AffineSubspace k P} (hs : (s : Set P).Nonempty) :
    asymptoticCone k (s : Set P) = closure s.direction := by
  have ⟨p, hp⟩ := hs
  ext v
  simp_rw [← asymptoticCone_submodule, mem_asymptoticCone_iff, ← asymptoticNhds_vadd_pure v p,
    vadd_pure, frequently_map, SetLike.mem_coe, s.vadd_mem_iff_mem_direction _ hp]

@[simp]
theorem asymptoticCone_univ : asymptoticCone k (Set.univ : Set P) = Set.univ := by
  rw [← AffineSubspace.top_coe k, asymptoticCone_affineSubspace Set.univ_nonempty,
    AffineSubspace.direction_top, Submodule.top_coe, closure_univ]

theorem asymptoticCone_closure [TopologicalSpace P] [IsTopologicalAddTorsor P] (s : Set P) :
    asymptoticCone k (closure s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, mem_closure_iff_frequently, ← frequently_bind,
    asymptoticNhds_bind_nhds]

theorem isClosed_asymptoticCone {s : Set P} : IsClosed (asymptoticCone k s) := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [isClosed_iff_frequently]
  intro v h
  simp_rw [mem_asymptoticCone_iff, ← frequently_bind, nhds_bind_asymptoticNhds] at h
  exact h

@[simp]
theorem asymptoticCone_asymptoticCone (s : Set P) :
    asymptoticCone k (asymptoticCone k s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, ← Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds]

end General

section Convex

open AffineSpace

variable
  {k V : Type*}
  [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V]
  {s : Set V}

/-- If a closed set `s` is star-convex at `p` and `v` is in the asymptotic cone of `s`, then the ray
of direction `v` starting from `p` is contained in `s`. -/
theorem StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : StarConvex k p s) (hs₂ : IsClosed s) (hc : 0 ≤ c) (hv : v ∈ asymptoticCone k s) :
    c • v +ᵥ p ∈ s := by
  refine isClosed_iff_frequently.mp hs₂ _ <|
    tendsto_snd (f := atTop (α := k)) |>.const_smul _ |>.vadd_const _ |>.frequently ?_
  rw [mem_asymptoticCone_iff, asymptoticNhds_eq_smul_vadd v p, vadd_pure, frequently_map,
    ← map₂_smul, ← map_prod_eq_map₂, frequently_map] at hv
  apply hv.mp
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop c)]
    with ⟨t, u⟩ (ht : c ≤ t) (h : t • u +ᵥ p ∈ s)
  change c • u +ᵥ p ∈ s
  apply hs₁.segment_subset h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub, vadd_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).nonneg_smul_right (sub_nonneg.mpr ht)

/-- If `v` is in the asymptotic cone of a closed convex set `s`, then for every `p ∈ s`, the ray of
direction `v` starting from `p` is contained in `s`. -/
theorem Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : Convex k s) (hs₂ : IsClosed s) (hc : 0 ≤ c) (hv : v ∈ asymptoticCone k s) (hp : p ∈ s) :
    c • v +ᵥ p ∈ s :=
  (hs₁ hp).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs₂ hc hv

protected theorem Convex.asymptoticCone (hs : Convex k s) : Convex k (asymptoticCone k s) := by
  wlog hs' : IsClosed s generalizing s
  · rw [← asymptoticCone_closure]; exact this hs.closure isClosed_closure
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [asymptoticCone_empty]; exact convex_empty
  intro v hv u hu a b ha hb hab
  rw [mem_asymptoticCone_iff]
  refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds _ |>.asymptoticNhds_vadd_const p
    |>.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 0] with c hc
  simp_rw [id, smul_add, smul_smul]
  have h₁ : c • v +ᵥ p ∈ s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hv hp
  have h₂ : c • u +ᵥ p ∈ s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hu hp
  apply hs.segment_subset h₁ h₂
  rw [← affineSegment_eq_segment, mem_vadd_const_affineSegment, affineSegment_eq_segment]
  exists a, b, ha, hb, hab
  module

/-- If `v` is in the asymptotic cone of a convex set `s`, then for every interior point `p`, the ray
of direction `v` starting from `p` is contained in `s`. -/
theorem Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone {c : k} {v p : V}
    (hs : Convex k s) (hc : 0 ≤ c) (hp : s ∈ 𝓝 p) (hv : v ∈ asymptoticCone k s) :
    c • v +ᵥ p ∈ s := by
  rw [mem_asymptoticCone_iff, asymptoticNhds_eq_smul_vadd v (c • v +ᵥ p), vadd_pure,
    frequently_map, ← map₂_smul, ← map_prod_eq_map₂, frequently_map] at hv
  refine frequently_const.mp (hv.mp ?_)
  have : Tendsto (fun u => -(c • u : V) +ᵥ c • v +ᵥ p) (𝓝 v) (𝓝 p) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [tendsto_fst.eventually <| eventually_gt_atTop 0, this.comp tendsto_snd hp]
    with ⟨t, u⟩ (ht : 0 < t) (hu : -(c • u) +ᵥ c • v +ᵥ p ∈ s) (h : t • u +ᵥ c • v +ᵥ p ∈ s)
  apply hs.segment_subset hu h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub]
  rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_neg, vadd_vsub]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).pos_smul_right ht

end Convex
