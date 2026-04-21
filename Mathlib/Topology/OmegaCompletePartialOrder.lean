/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Topology.Order.ScottTopology

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

* https://ncatlab.org/nlab/show/Scott+topology

-/

@[expose] public section

open Set OmegaCompletePartialOrder Topology

universe u

open Topology.IsScott in
@[simp] lemma Topology.IsScott.ωScottContinuous_iff_continuous {α : Type*}
    [OmegaCompletePartialOrder α] [TopologicalSpace α]
    [Topology.IsScott α (Set.range fun c : Chain α => Set.range c)] {f : α → Prop} :
    ωScottContinuous f ↔ Continuous f := by
  rw [ωScottContinuous, scottContinuousOn_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]

namespace Scott

/-- `x` is an `ω`-Sup of a chain `c` if it is the least upper bound of the range of `c`. -/
def IsωSup {α : Type u} [Preorder α] (c : Chain α) (x : α) : Prop :=
  (∀ i, c i ≤ x) ∧ ∀ y, (∀ i, c i ≤ y) → x ≤ y

theorem isωSup_iff_isLUB {α : Type u} [Preorder α] {c : Chain α} {x : α} :
    IsωSup c x ↔ IsLUB (range c) x := by
  simp [IsωSup, IsLUB, IsLeast, upperBounds, lowerBounds]

variable (α : Type u) [OmegaCompletePartialOrder α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def IsOpen (s : Set α) : Prop :=
  ωScottContinuous fun x ↦ x ∈ s

theorem isOpen_univ : IsOpen α univ := @CompleteLattice.ωScottContinuous.top α Prop _ _

theorem IsOpen.inter (s t : Set α) : IsOpen α s → IsOpen α t → IsOpen α (s ∩ t) :=
  CompleteLattice.ωScottContinuous.inf

theorem isOpen_sUnion (s : Set (Set α)) (hs : ∀ t ∈ s, IsOpen α t) : IsOpen α (⋃₀ s) := by
  simp only [IsOpen] at hs ⊢
  convert CompleteLattice.ωScottContinuous.sSup hs
  aesop

theorem IsOpen.isUpperSet {s : Set α} (hs : IsOpen α s) : IsUpperSet s := hs.monotone

end Scott

open Scott hiding IsOpen IsOpen.isUpperSet

theorem isωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
  · apply ωSup_le
