/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuousWithinAt_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuousWithinAt_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuousAt_iff_continuous_left_right`, `continuousAt_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/

@[expose] public section


open Set Filter Topology

section Preorder

variable {α : Type*} [TopologicalSpace α] [Preorder α]

lemma frequently_lt_nhds (a : α) [NeBot (𝓝[<] a)] : ∃ᶠ x in 𝓝 a, x < a :=
  frequently_iff_neBot.2 ‹_›

lemma frequently_gt_nhds (a : α) [NeBot (𝓝[>] a)] : ∃ᶠ x in 𝓝 a, a < x :=
  frequently_iff_neBot.2 ‹_›

theorem Filter.Eventually.exists_lt {a : α} [NeBot (𝓝[<] a)] {p : α → Prop}
    (h : ∀ᶠ x in 𝓝 a, p x) : ∃ b < a, p b :=
  ((frequently_lt_nhds a).and_eventually h).exists

theorem Filter.Eventually.exists_gt {a : α} [NeBot (𝓝[>] a)] {p : α → Prop}
    (h : ∀ᶠ x in 𝓝 a, p x) : ∃ b > a, p b :=
  ((frequently_gt_nhds a).and_eventually h).exists

theorem nhdsWithin_Ici_neBot {a b : α} (H₂ : a ≤ b) : NeBot (𝓝[Ici a] b) :=
  nhdsWithin_neBot_of_mem H₂

instance nhdsGE_neBot (a : α) : NeBot (𝓝[≥] a) := nhdsWithin_Ici_neBot (le_refl a)

theorem nhdsWithin_Iic_neBot {a b : α} (H : a ≤ b) : NeBot (𝓝[Iic b] a) :=
  nhdsWithin_neBot_of_mem H

instance nhdsLE_neBot (a : α) : NeBot (𝓝[≤] a) := nhdsWithin_Iic_neBot (le_refl a)

theorem nhdsLT_le_nhdsNE (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_lt

theorem nhdsGT_le_nhdsNE (a : α) : 𝓝[>] a ≤ 𝓝[≠] a := nhdsWithin_mono a fun _ => ne_of_gt

-- TODO: add instances for `NeBot (𝓝[<] x)` on (indexed) product types

lemma IsAntichain.interior_eq_empty [∀ x : α, (𝓝[<] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have : ∀ᶠ y in 𝓝 x, y ∈ s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le

lemma IsAntichain.interior_eq_empty' [∀ x : α, (𝓝[>] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ ?_
  have : ∀ᶠ y in 𝓝 x, y ∈ s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_gt with ⟨y, hyx, hys⟩
  exact hs (interior_subset hx) hys hyx.ne hyx.le

end Preorder

section PartialOrder

variable {α β : Type*} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_diff_left, continuousWithinAt_diff_self]

theorem continuousWithinAt_Iio_iff_Iic {a : α} {f : α → β} :
    ContinuousWithinAt f (Iio a) a ↔ ContinuousWithinAt f (Iic a) a := by
  simp only [← Iic_diff_right, continuousWithinAt_diff_self]

theorem continuousWithinAt_inter_Ioi_iff_Ici {a : α} {f : α → β} {s : Set α} :
    ContinuousWithinAt f (s ∩ Ioi a) a ↔ ContinuousWithinAt f (s ∩ Ici a) a := by
  simp [← Ici_diff_left, ← inter_diff_assoc, continuousWithinAt_diff_self]

theorem continuousWithinAt_inter_Iio_iff_Iic {a : α} {f : α → β} {s : Set α} :
    ContinuousWithinAt f (s ∩ Iio a) a ↔ ContinuousWithinAt f (s ∩ Iic a) a := by
  simp [← Iic_diff_right, ← inter_diff_assoc, continuousWithinAt_diff_self]

end PartialOrder

section TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β] {s : Set α}

theorem nhdsLE_sup_nhdsGE (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]

theorem nhdsWithinLE_sup_nhdsWithinGE (a : α) : 𝓝[s ∩ Iic a] a ⊔ 𝓝[s ∩ Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iic_union_Ici, inter_univ]

theorem nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]

theorem nhdsWithinLT_sup_nhdsWithinGE (a : α) : 𝓝[s ∩ Iio a] a ⊔ 𝓝[s ∩ Ici a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iio_union_Ici, inter_univ]

theorem nhdsLE_sup_nhdsGT (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]

theorem nhdsWithinLE_sup_nhdsWithinGT (a : α) : 𝓝[s ∩ Iic a] a ⊔ 𝓝[s ∩ Ioi a] a = 𝓝[s] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iic_union_Ioi, inter_univ]

theorem nhdsLT_sup_nhdsGT (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]

theorem nhdsWithinLT_sup_nhdsWithinGT (a : α) :
    𝓝[s ∩ Iio a] a ⊔ 𝓝[s ∩ Ioi a] a = 𝓝[s \ {a}] a := by
  rw [← nhdsWithin_union, ← inter_union_distrib_left, Iio_union_Ioi, compl_eq_univ_diff,
    inter_sdiff_left_comm, univ_inter]

lemma nhdsGT_sup_nhdsWithin_singleton (a : α) :
    𝓝[>] a ⊔ 𝓝[{a}] a = 𝓝[≥] a := by
  simp only [union_singleton, Ioi_insert, ← nhdsWithin_union]

lemma nhdsWithin_uIoo_left_le_nhdsNE {a b : α} : 𝓝[uIoo a b] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono _ (by simp)

lemma nhdsWithin_uIoo_right_le_nhdsNE {a b : α} : 𝓝[uIoo a b] b ≤ 𝓝[≠] b :=
  nhdsWithin_mono _ (by simp)

theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhdsLE_sup_nhdsGE]

theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Iio_iff_Iic,
    continuousAt_iff_continuous_left_right]

theorem continuousWithinAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s ∩ Iic a) a ∧ ContinuousWithinAt f (s ∩ Ici a) a := by
  simp only [ContinuousWithinAt, ← tendsto_sup, nhdsWithinLE_sup_nhdsWithinGE]

theorem continuousWithinAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousWithinAt f s a ↔
      ContinuousWithinAt f (s ∩ Iio a) a ∧ ContinuousWithinAt f (s ∩ Ioi a) a := by
  rw [continuousWithinAt_inter_Ioi_iff_Ici, continuousWithinAt_inter_Iio_iff_Iic,
    continuousWithinAt_iff_continuous_left_right]

end TopologicalSpace
