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

section PartialOrder

variable {α β : Type*} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

theorem continuousWithinAt_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_diff_left, continuousWithinAt_diff_self]
  -- 🎉 no goals
#align continuous_within_at_Ioi_iff_Ici continuousWithinAt_Ioi_iff_Ici

theorem continuousWithinAt_Iio_iff_Iic {a : α} {f : α → β} :
    ContinuousWithinAt f (Iio a) a ↔ ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_Ioi_iff_Ici αᵒᵈ _ _ _ _ _ f
#align continuous_within_at_Iio_iff_Iic continuousWithinAt_Iio_iff_Iic

theorem nhds_left'_le_nhds_ne (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_lt
#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_ne

theorem nhds_right'_le_nhds_ne (a : α) : 𝓝[>] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun _ => ne_of_gt
#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_ne

end PartialOrder

section TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]

theorem nhds_left_sup_nhds_right (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]
  -- 🎉 no goals
#align nhds_left_sup_nhds_right nhds_left_sup_nhds_right

theorem nhds_left'_sup_nhds_right (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]
  -- 🎉 no goals
#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_right

theorem nhds_left_sup_nhds_right' (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]
  -- 🎉 no goals
#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'

theorem nhds_left'_sup_nhds_right' (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]
  -- 🎉 no goals
#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'

theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhds_left_sup_nhds_right]
  -- 🎉 no goals
#align continuous_at_iff_continuous_left_right continuousAt_iff_continuous_left_right

theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Iio_iff_Iic,
    continuousAt_iff_continuous_left_right]
#align continuous_at_iff_continuous_left'_right' continuousAt_iff_continuous_left'_right'

end TopologicalSpace
