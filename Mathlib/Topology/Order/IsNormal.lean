/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.IsNormal
import Mathlib.Topology.Order.IsLUB

/-!
# A normal function is strictly monotone and continuous

We defined the predicate `Order.IsNormal` in terms of `IsLUB`, which avoids having to import
topology in order theory files. This file shows that the predicate is equivalent to the definition
in the literature, being that of a strictly monotonic function, continuous in the order topology.
-/

open Set

namespace Order
variable {α β : Type*}
  [LinearOrder α] [WellFoundedLT α] [TopologicalSpace α] [OrderTopology α]
  [LinearOrder β] [WellFoundedLT β] [TopologicalSpace β] [OrderTopology β]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
theorem IsNormal.continuous {f : α → β} (hf : IsNormal f) : Continuous f := by
  rw [OrderTopology.continuous_iff]
  refine fun b ↦ ⟨?_, ((isLowerSet_Iio b).preimage hf.strictMono.monotone).isOpen⟩
  rw [← isClosed_compl_iff, ← Set.preimage_compl, Set.compl_Ioi]
  obtain ha | ⟨a, ha⟩ := ((isLowerSet_Iic b).preimage hf.strictMono.monotone).eq_univ_or_Iio
  · exact ha ▸ isClosed_univ
  · obtain h | h := (f ⁻¹' Iic b).eq_empty_or_nonempty
    · exact h ▸ isClosed_empty
    · have : Nonempty α := ⟨a⟩
      have : Nonempty β := ⟨b⟩
      rw [hf.preimage_Iic h (ha ▸ bddAbove_Iio)]
      exact isClosed_Iic

/-- A normal function between well-orders is equivalent to a strictly monotone,
continuous function. -/
theorem isNormal_iff_strictMono_and_continuous {f : α → β} :
    IsNormal f ↔ StrictMono f ∧ Continuous f where
  mp hf := ⟨hf.strictMono, hf.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha ↦ (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

end Order
