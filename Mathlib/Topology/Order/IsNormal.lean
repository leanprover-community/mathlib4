/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.IsNormal
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.ScottTopology

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# A normal function is strictly monotone and continuous

We defined the predicate `Order.IsNormal` in terms of `IsLUB`, which avoids having to import
topology in order theory files. This file shows that the predicate is equivalent to the definition
in the literature, being that of a strictly monotonic function, continuous in the order topology.
-/

public section

open Set

namespace Order
variable {α β : Type*}
  [LinearOrder α] [WellFoundedLT α] [TopologicalSpace α] [OrderTopology α]
  [LinearOrder β] [WellFoundedLT β] [TopologicalSpace β] [OrderTopology β]

@[deprecated Topology.IsScottHausdorff.continuous_of_leftOrdContinuous +typeChanged
(since := "2026-11-03")]
theorem IsNormal.continuous {f : α → β} (hf : IsNormal f) : Continuous f :=
  Topology.IsScottHausdorff.continuous_of_leftOrdContinuous hf.leftOrdContinuous

/-- A normal function between well-orders is equivalent to a strictly monotone,
continuous function. -/
theorem isNormal_iff_strictMono_and_continuous {f : α → β} :
    IsNormal f ↔ StrictMono f ∧ Continuous f where
  mp hf := ⟨hf.strictMono, hf.leftOrdContinuous.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha ↦ (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

end Order
