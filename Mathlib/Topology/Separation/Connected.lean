/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Perfect

/-!
# Interaction of separation properties with connectedness properties
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

open Filter Set
open scoped Topology

-- see Note [lower instance priority]
instance (priority := 100) TotallyDisconnectedSpace.t1Space [h : TotallyDisconnectedSpace X] :
    T1Space X := by
  rw [((t1Space_TFAE X).out 0 1 :)]
  intro x
  rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.mp h x]
  exact isClosed_connectedComponent

theorem PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopology X] :
    Subsingleton X := by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne, ← mem_singleton_iff, (isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)

theorem IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreconnected s)
    (hs : s.Nontrivial) : s.Infinite := by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  haveI := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _

theorem PreconnectedSpace.infinite [PreconnectedSpace X] [Nontrivial X] [T1Space X] : Infinite X :=
  infinite_univ_iff.mp <| isPreconnected_univ.infinite_of_nontrivial nontrivial_univ

/-- A non-trivial connected T1 space has no isolated points.

This is now a consequence of the `PerfectSpace` instance for connected T1 nontrivial spaces
defined in `Mathlib.Topology.Perfect`. -/
example [ConnectedSpace X] [Nontrivial X] [T1Space X] (x : X) :
    NeBot (𝓝[≠] x) := inferInstance
