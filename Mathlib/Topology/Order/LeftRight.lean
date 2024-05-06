/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.ContinuousOn

#align_import topology.algebra.order.left_right from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

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
#align filter.eventually.exists_lt Filter.Eventually.exists_lt

theorem Filter.Eventually.exists_gt {a : α} [NeBot (𝓝[>] a)] {p : α → Prop}
    (h : ∀ᶠ x in 𝓝 a, p x) : ∃ b > a, p b :=
  ((frequently_gt_nhds a).and_eventually h).exists
#align filter.eventually.exists_gt Filter.Eventually.exists_gt

theorem nhdsWithin_Ici_neBot {a b : α} (H₂ : a ≤ b) : NeBot (𝓝[Ici a] b) :=
  nhdsWithin_neBot_of_mem H₂
#align nhds_within_Ici_ne_bot nhdsWithin_Ici_neBot

instance nhdsWithin_Ici_self_neBot (a : α) : NeBot (𝓝[≥] a) :=
  nhdsWithin_Ici_neBot (le_refl a)
#align nhds_within_Ici_self_ne_bot nhdsWithin_Ici_self_neBot

theorem nhdsWithin_Iic_neBot {a b : α} (H : a ≤ b) : NeBot (𝓝[Iic b] a) :=
  nhdsWithin_neBot_of_mem H
#align nhds_within_Iic_ne_bot nhdsWithin_Iic_neBot

instance nhdsWithin_Iic_self_neBot (a : α) : NeBot (𝓝[≤] a) :=
  nhdsWithin_Iic_neBot (le_refl a)
#align nhds_within_Iic_self_ne_bot nhdsWithin_Iic_self_neBot

theorem nhds_left'_le_nhds_ne (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_lt
#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_ne

theorem nhds_right'_le_nhds_ne (a : α) : 𝓝[>] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_gt
#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_ne

-- TODO: add instances for `NeBot (𝓝[<] x)` on (indexed) product types

lemma IsAntichain.interior_eq_empty [∀ x : α, (𝓝[<] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ := by
  refine eq_empty_of_forall_not_mem fun x hx ↦ ?_
  have : ∀ᶠ y in 𝓝 x, y ∈ s := mem_interior_iff_mem_nhds.1 hx
  rcases this.exists_lt with ⟨y, hyx, hys⟩
  exact hs hys (interior_subset hx) hyx.ne hyx.le
#align is_antichain.interior_eq_empty IsAntichain.interior_eq_empty

lemma IsAntichain.interior_eq_empty' [∀ x : α, (𝓝[>] x).NeBot] {s : Set α}
    (hs : IsAntichain (· ≤ ·) s) : interior s = ∅ :=
  have : ∀ x : αᵒᵈ, NeBot (𝓝[<] x) := ‹_›
  hs.to_dual.interior_eq_empty

end Preorder

section PartialOrder

variable {α β : Type*} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_diff_left, continuousWithinAt_diff_self]
#align continuous_within_at_Ioi_iff_Ici continuousWithinAt_Ioi_iff_Ici

theorem continuousWithinAt_Iio_iff_Iic {a : α} {f : α → β} :
    ContinuousWithinAt f (Iio a) a ↔ ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_Ioi_iff_Ici αᵒᵈ _ _ _ _ _ f
#align continuous_within_at_Iio_iff_Iic continuousWithinAt_Iio_iff_Iic

end PartialOrder

section TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]

theorem nhds_left_sup_nhds_right (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]
#align nhds_left_sup_nhds_right nhds_left_sup_nhds_right

theorem nhds_left'_sup_nhds_right (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]
#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_right

theorem nhds_left_sup_nhds_right' (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]
#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'

theorem nhds_left'_sup_nhds_right' (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]
#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'

theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhds_left_sup_nhds_right]
#align continuous_at_iff_continuous_left_right continuousAt_iff_continuous_left_right

theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Iio_iff_Iic,
    continuousAt_iff_continuous_left_right]
#align continuous_at_iff_continuous_left'_right' continuousAt_iff_continuous_left'_right'

end TopologicalSpace
