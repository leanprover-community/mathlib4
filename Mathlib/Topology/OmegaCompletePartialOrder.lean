/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.Order.ScottTopology

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

* https://ncatlab.org/nlab/show/Scott+topology

-/

open Set OmegaCompletePartialOrder

universe u

open Topology.IsScott in
@[simp] lemma Topology.IsScott.ωscottContinuous_iff_continuous {α : Type*}
    [OmegaCompletePartialOrder α] [TopologicalSpace α]
    [Topology.IsScott α (Set.range fun c : Chain α => Set.range c)] {f : α → Prop} :
    ωScottContinuous f ↔ Continuous f := by
  rw [ωScottContinuous, scottContinuous_iff_continuous (fun a b hab => by
    use Chain.pair a b hab; exact OmegaCompletePartialOrder.Chain.range_pair a b hab)]

-- "Scott", "ωSup"
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

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains. -/
abbrev Scott (α : Type u) := α

instance Scott.topologicalSpace (α : Type u) [OmegaCompletePartialOrder α] :
    TopologicalSpace (Scott α) where
  IsOpen := Scott.IsOpen α
  isOpen_univ := Scott.isOpen_univ α
  isOpen_inter := Scott.IsOpen.inter α
  isOpen_sUnion := Scott.isOpen_sUnion α

lemma isOpen_iff_ωScottContinuous_mem {α} [OmegaCompletePartialOrder α] {s : Set (Scott α)} :
    IsOpen s ↔ ωScottContinuous fun x ↦ x ∈ s := by rfl

lemma scott_eq_Scott {α} [OmegaCompletePartialOrder α] :
    Topology.scott α (Set.range fun c : Chain α => Set.range c) = Scott.topologicalSpace α := by
  ext U
  letI := Topology.scott α (Set.range fun c : Chain α => Set.range c)
  rw [isOpen_iff_ωScottContinuous_mem, @isOpen_iff_continuous_mem,
    @Topology.IsScott.ωscottContinuous_iff_continuous _ _
      (Topology.scott α (Set.range fun c : Chain α => Set.range c)) ({ topology_eq_scott := rfl })]

section notBelow

variable {α : Type*} [OmegaCompletePartialOrder α] (y : Scott α)

/-- `notBelow` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def notBelow :=
  { x | ¬x ≤ y }

theorem notBelow_isOpen : IsOpen (notBelow y) := by
  have h : Monotone (notBelow y) := fun x z hle ↦ mt hle.trans
  dsimp only [IsOpen, TopologicalSpace.IsOpen, Scott.IsOpen]
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨h, fun c ↦ eq_of_forall_ge_iff fun z ↦ ?_⟩
  simp only [ωSup_le_iff, notBelow, mem_setOf_eq, le_Prop_eq, OrderHom.coe_mk, Chain.map_coe,
    Function.comp_apply, exists_imp, not_forall]

end notBelow

open Scott hiding IsOpen IsOpen.isUpperSet

theorem isωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
  · apply ωSup_le

theorem scottContinuous_of_continuous {α β} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f : Scott α → Scott β) (hf : _root_.Continuous f) :
    OmegaCompletePartialOrder.ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  have h : Monotone f := fun x y h ↦ by
    have hf : IsUpperSet {x | ¬f x ≤ f y} := ((notBelow_isOpen (f y)).preimage hf).isUpperSet
    simpa only [mem_setOf_eq, le_refl, not_true, imp_false, not_not] using hf h
  refine ⟨h, fun c ↦ eq_of_forall_ge_iff fun z ↦ ?_⟩
  rcases (notBelow_isOpen z).preimage hf with hf''
  let hf' := hf''.monotone_map_ωSup.2
  specialize hf' c
  simp only [OrderHom.coe_mk, mem_preimage, notBelow, mem_setOf_eq] at hf'
  rw [← not_iff_not]
  simp only [ωSup_le_iff, hf', ωSup, iSup, sSup, mem_range, Chain.map_coe, Function.comp_apply,
    eq_iff_iff, not_forall, OrderHom.coe_mk]
  tauto

theorem continuous_of_scottContinuous {α β} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f : Scott α → Scott β) (hf : ωScottContinuous f) :
    Continuous f := by
  rw [continuous_def]; exact fun s hs ↦ hs.comp hf
