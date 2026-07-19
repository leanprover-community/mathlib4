/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Order.T5

/-!
# Hereditary separability of linear orders

In this file we prove some results about a separable linearly ordered topological space.

## Main results

* `exists_isOpen_ordConnected_mem_subset`: every point of an open set has an open order connected
  neighbourhood contained in that set.
* `isTopologicalBasis_isOpen_ordConnected`: the open order connected sets form a topological basis.
* `countable_setOf_isolated_subtype`: in a separable linearly ordered topological space, the
  points of a subset that are isolated in the subspace topology form a countable set.
* `Set.separableSpace`: a separable linearly ordered topological space is hereditarily separable.

-/

public section

open Filter Set TopologicalSpace
open scoped Topology

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

section OrdConnected

/-- Every point `x` of an open set `U` has an open order connected neighbourhood contained in `U`.
-/
theorem exists_isOpen_ordConnected_mem_subset {U : Set α} (hU : IsOpen U) {x : α} (hx : x ∈ U) :
    ∃ V, IsOpen V ∧ V.OrdConnected ∧ x ∈ V ∧ V ⊆ U := by
  refine ⟨interior (ordConnectedComponent U x), isOpen_interior, ⟨fun y hy z hz w hw ↦ ?_⟩,
    mem_interior_iff_mem_nhds.2 (ordConnectedComponent_mem_nhds.2 (hU.mem_nhds hx)),
    interior_subset.trans ordConnectedComponent_subset⟩
  rcases hw.1.eq_or_lt with rfl | hyw
  · exact hy
  rcases hw.2.eq_or_lt with rfl | hwz
  · exact hz
  exact mem_interior.2 ⟨Ioo y z, fun v hv ↦ OrdConnected.out inferInstance
    (interior_subset hy) (interior_subset hz) ⟨hv.1.le, hv.2.le⟩, isOpen_Ioo, hyw, hwz⟩

/-- The open order connected sets form a topological basis of a linearly ordered topological
space. -/
theorem isTopologicalBasis_isOpen_ordConnected :
    IsTopologicalBasis {V : Set α | IsOpen V ∧ V.OrdConnected} :=
  isTopologicalBasis_of_isOpen_of_nhds (fun _ hu ↦ hu.1) fun _ _ ha hu ↦
    let ⟨V, hVo, hVc, haV, hVu⟩ := exists_isOpen_ordConnected_mem_subset hu ha
    ⟨V, ⟨hVo, hVc⟩, haV, hVu⟩

/-- The open order connected sets containing a point form a basis of its neighbourhood filter. -/
theorem nhds_basis_isOpen_ordConnected (x : α) :
    (𝓝 x).HasBasis (fun V : Set α ↦ (IsOpen V ∧ V.OrdConnected) ∧ x ∈ V) id :=
  isTopologicalBasis_isOpen_ordConnected.nhds_hasBasis

end OrdConnected

section Separable

/-- In a separable linearly ordered topological space, the points of a subset `s` that are
isolated in the subspace `↥s` form a countable set.

Each such point `x` has an open order connected neighbourhood `W x` meeting `s` only in `x`. The
sets `W x ∩ Ioi x` are then pairwise disjoint, as are the sets `W x ∩ Iio x`, so in a separable
space only countably many of each are nonempty; and if both are empty then `W x = {x}` is open,
so `x` belongs to any dense set. -/
theorem countable_setOf_isolated_subtype [SeparableSpace α] (s : Set α) :
    {x : s | IsOpen {x}}.Countable := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense α
  have key (x : s) (hx : IsOpen {x}) :
      ∃ W, IsOpen W ∧ W.OrdConnected ∧ x.1 ∈ W ∧ W ∩ s ⊆ {x.1} := by
    obtain ⟨U, hU, hUx⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hx
    have hUs : U ∩ s ⊆ {(x : α)} := fun z hz ↦
      congrArg Subtype.val (hUx.le (show (⟨z, hz.2⟩ : s) ∈ Subtype.val ⁻¹' U from hz.1))
    obtain ⟨W, hWo, hWc, hWx, hWU⟩ := exists_isOpen_ordConnected_mem_subset hU (hUx.ge rfl)
    exact ⟨W, hWo, hWc, hWx, (inter_subset_inter_left s hWU).trans hUs⟩
  choose! W hWo hWc hWx hWs using key
  -- no isolated point above `x` is caught by `W x`, and none below
  have hup : ∀ x : s, IsOpen {x} → ∀ y : s, (x : α) < (y : α) →
      ∀ z ∈ W x, ¬ (y : α) ≤ z := fun x hx y hxy z hz hyz ↦
    hxy.ne' (hWs x hx ⟨(hWc x hx).out (hWx x hx) hz ⟨hxy.le, hyz⟩, y.2⟩)
  have hdown : ∀ x : s, IsOpen {x} → ∀ y : s, (y : α) < (x : α) →
      ∀ z ∈ W x, ¬ z ≤ (y : α) := fun x hx y hyx z hz hzy ↦
    hyx.ne (hWs x hx ⟨(hWc x hx).out hz (hWx x hx) ⟨hzy, hyx.le⟩, y.2⟩)
  have hcr : {x : s | IsOpen {x} ∧ (W x ∩ Ioi (x : α)).Nonempty}.Countable := by
    refine PairwiseDisjoint.countable_of_isOpen (s := fun x : s ↦ W x ∩ Ioi (x : α)) ?_
      (fun x hx ↦ (hWo x hx.1).inter isOpen_Ioi) fun x hx ↦ hx.2
    rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    refine disjoint_left.2 fun z hzx hzy ↦ ?_
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hxy) with h | h
    · exact hup x hx y h z hzx.1 hzy.2.le
    · exact hup y hy x h z hzy.1 hzx.2.le
  have hcl : {x : s | IsOpen {x} ∧ (W x ∩ Iio x).Nonempty}.Countable := by
    refine PairwiseDisjoint.countable_of_isOpen (s := fun x : s ↦ W x ∩ Iio (x : α)) ?_
      (fun x hx ↦ (hWo x hx.1).inter isOpen_Iio) fun x hx ↦ hx.2
    rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    refine disjoint_left.2 fun z hzx hzy ↦ ?_
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hxy) with h | h
    · exact hdown y hy x h z hzy.1 hzx.2.le
    · exact hdown x hx y h z hzx.1 hzy.2.le
  -- an isolated point with nothing of `W x` on either side is isolated in `α`, hence lies in `D`
  refine ((hcr.union hcl).union (hDc.preimage Subtype.val_injective)).mono fun x hx ↦ ?_
  rcases (W x ∩ Ioi x).eq_empty_or_nonempty with h₁ | h₁
  swap
  · exact Or.inl (Or.inl ⟨hx, h₁⟩)
  rcases (W x ∩ Iio x).eq_empty_or_nonempty with h₂ | h₂
  swap
  · exact Or.inl (Or.inr ⟨hx, h₂⟩)
  have hsing : W x = {x.1} := calc
    _ = W x ∩ Iio x ∪ W x ∩ {x.1} ∪ W x ∩ Ioi x := by grind
    _ = {x.1} := by grind
  exact Or.inr (hDd.mem_of_isOpen_singleton (hsing ▸ hWo x hx))

/-- A separable linearly ordered topological space is hereditarily separable: every subset,
equipped with the subspace topology, is a separable space. -/
instance Set.separableSpace [SeparableSpace α] (s : Set α) : SeparableSpace s := by
  obtain ⟨D, hc, hd⟩ := exists_countable_dense α
  -- a point of `s` strictly between `p` and `q`, whenever there is one
  have hchoice (p q) : ∃ z : α, (s ∩ Ioo p q).Nonempty → z ∈ s ∩ Ioo p q := by
    by_cases h : (s ∩ Ioo p q).Nonempty
    · exact ⟨h.choose, fun _ ↦ h.choose_spec⟩
    · exact ⟨p, fun h' ↦ absurd h' h⟩
  choose a ha using hchoice
  refine ⟨⟨{x : s | IsOpen {x}} ∪ Subtype.val ⁻¹' image2 a D D,
    (countable_setOf_isolated_subtype s).union
    ((hc.image2 hc a).preimage Subtype.val_injective), ?_⟩⟩
  refine dense_iff_inter_open.2 fun O hO ⟨x, hxO⟩ ↦ ?_
  by_cases hxiso : IsOpen {x}
  · exact ⟨x, hxO, Or.inl hxiso⟩
  obtain ⟨U, hU, hUO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hO
  obtain ⟨W, hWo, hWc, hWx, hWU⟩ := exists_isOpen_ordConnected_mem_subset hU (hUO.ge hxO)
  -- as `x` is not isolated in `s`, every open set containing it meets `s` in a different point
  have hnot (G : Set α) (hG : IsOpen G) (hxG : x.1 ∈ G) : ∃ y ∈ s, y ∈ G ∧ y ≠ x := by
    by_contra! hcon
    suffices hGx : Subtype.val ⁻¹' G = {x} from hxiso (hGx ▸ hG.preimage continuous_subtype_val)
    grind
  -- a point `b` of `s` in `W` with points of `W` strictly on either side of it
  obtain ⟨b, hbs, hlo, hhi⟩ : ∃ b ∈ s, (W ∩ Iio b).Nonempty ∧ (W ∩ Ioi b).Nonempty := by
    obtain ⟨y, hys, hyW, hyx⟩ := hnot W hWo hWx
    rcases hyx.lt_or_gt with hy | hy
    · obtain ⟨z, hzs, hzW, hzx⟩ := hnot (W ∩ Ioi y) (hWo.inter isOpen_Ioi) ⟨hWx, hy⟩
      rcases hzx.lt_or_gt with hz | hz
      · exact ⟨z, hzs, ⟨y, hyW, hzW.2⟩, ⟨x, hWx, hz⟩⟩
      · exact ⟨x, x.2, ⟨y, hyW, hy⟩, ⟨z, hzW.1, hz⟩⟩
    · obtain ⟨z, hzs, hzW, hzx⟩ := hnot (W ∩ Iio y) (hWo.inter isOpen_Iio) ⟨hWx, hy⟩
      rcases hzx.lt_or_gt with hz | hz
      · exact ⟨x, x.2, ⟨z, hzW.1, hz⟩, ⟨y, hyW, hy⟩⟩
      · exact ⟨z, hzs, ⟨x, hWx, hz⟩, ⟨y, hyW, hzW.2⟩⟩
  obtain ⟨p, hpD, hpW⟩ := hd.exists_mem_open (hWo.inter isOpen_Iio) hlo
  obtain ⟨q, hqD, hqW⟩ := hd.exists_mem_open (hWo.inter isOpen_Ioi) hhi
  obtain ⟨hasq, hapq⟩ := ha p q ⟨b, hbs, hpW.2, hqW.2⟩
  exact ⟨⟨a p q, hasq⟩,
    hUO.le (hWU (hWc.out hpW.1 hqW.1 (Ioo_subset_Icc_self hapq))),
    Or.inr ⟨p, hpD, q, hqD, rfl⟩⟩

end Separable
