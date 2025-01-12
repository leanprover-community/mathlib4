/-
Copyright (c) 2024 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuity of indicator functions
-/

open Set
open scoped Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s : Set α} [One β]

@[to_additive]
lemma continuous_mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : ContinuousOn f (closure s)) :
    Continuous (mulIndicator s f) := by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]
protected lemma Continuous.mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const

@[to_additive]
theorem ContinuousOn.continuousAt_mulIndicator (hf : ContinuousOn f (interior s)) {x : α}
    (hx : x ∉ frontier s) :
    ContinuousAt (s.mulIndicator f) x := by
  rw [← Set.mem_compl_iff, compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
    exact ContinuousAt.congr (hf.continuousAt hs) <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
  · exact ContinuousAt.congr continuousAt_const <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

namespace IsClopen

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [One Y]

/-- The continuous function which is equal to `y` on the clopen set `U` and one elsewhere. -/
@[to_additive "The continuous function which is equal to `y` on the clopen set `U` and zero
elsewhere."]
noncomputable def constMulIndicator {U : Set X} (hU : IsClopen U) (y : Y) : C(X, Y) :=
  have : frontier U = ∅ := by simp [hU]
  ⟨U.mulIndicator (fun _ ↦ y), continuous_const.mulIndicator (by simp [this]) ⟩

@[to_additive]
lemma constMulIndicator_of_mem {U : Set X} (hU : IsClopen U) {y : Y} {x : X} (hx : x ∈ U) :
    hU.constMulIndicator y x = y :=
  mulIndicator_of_mem hx (fun _ ↦ y)

@[to_additive]
lemma constMulIndicator_of_not_mem {U : Set X} (hU : IsClopen U) {y : Y} {x : X} (hx : x ∉ U) :
    hU.constMulIndicator y x = 1 :=
  mulIndicator_of_not_mem hx (fun _ ↦ y)

end IsClopen
