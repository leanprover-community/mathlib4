/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Order.LiminfLimsup

/-!
# Relating order and metric boundedness

In spaces equipped with both an order and a metric, there are separate notions of boundedness
associated with each of the two structures. In specific cases such as ℝ, there are results which
relate the two notions.

## Tags

bounded, bornology, order, metric
-/

open Set Filter

section Real

@[deprecated isBoundedUnder_of (since := "2024-06-07")]
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  obtain ⟨c, hc⟩ := h.bddAbove
  exact isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩

@[deprecated isBoundedUnder_of (since := "2024-06-07")]
lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  obtain ⟨c, hc⟩ := h.bddBelow
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩

end Real
