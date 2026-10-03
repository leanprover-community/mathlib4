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

private lemma countable_isolated_inter_Ioi_aux [SeparableSpace α] {s : Set α} {W : s → Set α}
    (hWo : ∀ x, IsOpen {x} → IsOpen (W x)) (hWc : ∀ x, IsOpen {x} → (W x).OrdConnected)
    (hWx : ∀ x, IsOpen {x} → {x.1} = W x ∩ s) :
    {x : s | IsOpen {x} ∧ (W x ∩ Ioi x).Nonempty}.Countable := by
  refine PairwiseDisjoint.countable_of_isOpen ?_ ?_ fun _ hx ↦ hx.2
  · rintro x ⟨hx, -⟩ y ⟨hy, -⟩ hxy
    refine disjoint_left.2 fun z hzx hzy ↦ ?_
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hxy) with h | h
    · exact h.ne' ((hWx x hx).ge
        ⟨(hWc x hx).out ((hWx x hx).le rfl).1 hzx.1 ⟨h.le, hzy.2.le⟩, y.2⟩)
    · exact h.ne' ((hWx y hy).ge
        ⟨(hWc y hy).out ((hWx y hy).le rfl).1 hzy.1 ⟨h.le, hzx.2.le⟩, x.2⟩)
  · exact fun x hx ↦ (hWo x hx.1).inter isOpen_Ioi

/-- In a separable linearly ordered topological space, the points of a subset `s` that are
isolated in the subspace `s` form a countable set. -/
theorem countable_setOf_isolated_subtype [SeparableSpace α] (s : Set α) :
    {x : s | IsOpen {x}}.Countable := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense α
  -- Each such point `x` has an open order connected neighbourhood `W x` meeting `s` only in `x`.
  have key (x : s) (hx : IsOpen {x}) : ∃ W, IsOpen W ∧ W.OrdConnected ∧ {x.1} = W ∩ s := by
    obtain ⟨U, hU, hUx⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hx
    obtain ⟨W, hWo, hWc, hxW, hWU⟩ := exists_isOpen_ordConnected_mem_subset hU (hUx.ge rfl)
    refine ⟨W, hWo, hWc, Subset.antisymm (fun _ h ↦ h ▸ ⟨hxW, x.2⟩) fun y hy ↦ ?_⟩
    exact congrArg Subtype.val <|
      hUx.le (show (⟨y, hy.2⟩ : s) ∈ Subtype.val ⁻¹' U from hWU hy.1)
  choose! W hWo hWc hWx using key
  -- The sets `W x ∩ Ioi x` are then pairwise disjoint, as are the sets `W x ∩ Iio x`.
  have hcr : {x : s | IsOpen {x} ∧ (W x ∩ Ioi x).Nonempty}.Countable :=
    countable_isolated_inter_Ioi_aux hWo hWc hWx
  have hcl : {x : s | IsOpen {x} ∧ (W x ∩ Iio x).Nonempty}.Countable :=
    countable_isolated_inter_Ioi_aux (α := αᵒᵈ) hWo (fun x hx ↦ (hWc x hx).dual) hWx
  -- An isolated point with nothing of `W x` on either side is isolated in `α`, hence lies in `D`.
  refine ((hcr.union hcl).union (hDc.preimage Subtype.val_injective)).mono fun x hx ↦ ?_
  rcases (W x ∩ Ioi x).eq_empty_or_nonempty with h₁ | h₁
  · rcases (W x ∩ Iio x).eq_empty_or_nonempty with h₂ | h₂
    · have hsing : W x = {x.1} := calc
        _ = W x ∩ Iio x ∪ W x ∩ {x.1} ∪ W x ∩ Ioi x := by grind
        _ = {x.1} := by grind
      exact .inr (hDd.mem_of_isOpen_singleton (hsing ▸ hWo x hx))
    · exact .inl (.inr ⟨hx, h₂⟩)
  · exact .inl (.inl ⟨hx, h₁⟩)

/-- A separable linearly ordered topological space is hereditarily separable: every subset,
equipped with the subspace topology, is a separable space. -/
instance Set.separableSpace [SeparableSpace α] (s : Set α) : SeparableSpace s := by
  obtain ⟨D, hc, hd⟩ := exists_countable_dense α
  -- A point of `s` strictly between `p` and `q`, whenever there is one.
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
  · exact ⟨x, hxO, .inl hxiso⟩
  obtain ⟨U, hU, hUO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hO
  obtain ⟨W, hWo, hWc, hWx, hWU⟩ := exists_isOpen_ordConnected_mem_subset hU (hUO.ge hxO)
  -- A point `b` of `s` in `W` with points of `W` strictly on either side of it.
  obtain ⟨b, hbs, hlo, hhi⟩ :
      ∃ b ∈ s, (W ∩ Iio b).Nonempty ∧ (W ∩ Ioi b).Nonempty := by
    rw [isOpen_singleton_iff_punctured_nhds] at hxiso
    let : NeBot (𝓝[≠] x) := ⟨hxiso⟩
    have hWinf : (Subtype.val ⁻¹' W).Infinite :=
      infinite_of_mem_nhds x ((hWo.preimage continuous_subtype_val).mem_nhds hWx)
    by_contra! h
    exact hWinf (finite_of_forall_not_lt_lt fun a ha b hb c hc hab hbc ↦
      (congrArg ((c : α) ∈ ·) (h b b.2 ⟨a, ha, hab⟩)).mp ⟨hc, hbc⟩)
  obtain ⟨p, hpD, hpW⟩ := hd.exists_mem_open (hWo.inter isOpen_Iio) hlo
  obtain ⟨q, hqD, hqW⟩ := hd.exists_mem_open (hWo.inter isOpen_Ioi) hhi
  obtain ⟨hasq, hapq⟩ := ha p q ⟨b, hbs, hpW.2, hqW.2⟩
  exact ⟨⟨a p q, hasq⟩, hUO.le (hWU (hWc.out hpW.1 hqW.1 (Ioo_subset_Icc_self hapq))),
    .inr ⟨p, hpD, q, hqD, rfl⟩⟩

end Separable
