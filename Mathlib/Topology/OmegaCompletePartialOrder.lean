/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Topology.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/


open Set OmegaCompletePartialOrder

open scoped Classical

universe u

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
  Continuous' fun x ↦ x ∈ s

theorem isOpen_univ : IsOpen α univ :=
  ⟨fun _ _ _ _ ↦ mem_univ _, @CompleteLattice.top_continuous α Prop _ _⟩

theorem IsOpen.inter (s t : Set α) : IsOpen α s → IsOpen α t → IsOpen α (s ∩ t) :=
  CompleteLattice.inf_continuous'

theorem isOpen_sUnion (s : Set (Set α)) (hs : ∀ t ∈ s, IsOpen α t) : IsOpen α (⋃₀ s) := by
  simp only [IsOpen] at hs ⊢
  convert CompleteLattice.sSup_continuous' (setOf ⁻¹' s) hs
  simp only [sSup_apply, setOf_bijective.surjective.exists, exists_prop, mem_preimage,
    SetCoe.exists, iSup_Prop_eq, mem_setOf_eq, mem_sUnion]

theorem IsOpen.isUpperSet {s : Set α} (hs : IsOpen α s) : IsUpperSet s := hs.fst

end Scott

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
abbrev Scott (α : Type u) := α

instance Scott.topologicalSpace (α : Type u) [OmegaCompletePartialOrder α] :
    TopologicalSpace (Scott α) where
  IsOpen := Scott.IsOpen α
  isOpen_univ := Scott.isOpen_univ α
  isOpen_inter := Scott.IsOpen.inter α
  isOpen_sUnion := Scott.isOpen_sUnion α

section notBelow

variable {α : Type*} [OmegaCompletePartialOrder α] (y : Scott α)

/-- `notBelow` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def notBelow :=
  { x | ¬x ≤ y }

theorem notBelow_isOpen : IsOpen (notBelow y) := by
  have h : Monotone (notBelow y) := fun x z hle ↦ mt hle.trans
  refine ⟨h, fun c ↦ eq_of_forall_ge_iff fun z ↦ ?_⟩
  simp only [ωSup_le_iff, notBelow, mem_setOf_eq, le_Prop_eq, OrderHom.coe_mk, Chain.map_coe,
    Function.comp_apply, exists_imp, not_forall]

end notBelow

open Scott hiding IsOpen

open OmegaCompletePartialOrder

theorem isωSup_ωSup {α} [OmegaCompletePartialOrder α] (c : Chain α) : IsωSup c (ωSup c) := by
  constructor
  · apply le_ωSup
  · apply ωSup_le

theorem scottContinuous_of_continuous {α β} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f : Scott α → Scott β) (hf : Continuous f) :
    OmegaCompletePartialOrder.Continuous' f := by
  have h : Monotone f := fun x y h ↦ by
    have hf : IsUpperSet {x | ¬f x ≤ f y} := ((notBelow_isOpen (f y)).preimage hf).isUpperSet
    simpa only [mem_setOf_eq, le_refl, not_true, imp_false, not_not] using hf h
  refine ⟨h, fun c ↦ eq_of_forall_ge_iff fun z ↦ ?_⟩
  rcases (notBelow_isOpen z).preimage hf with ⟨hf, hf'⟩
  specialize hf' c
  simp only [OrderHom.coe_mk, mem_preimage, notBelow, mem_setOf_eq] at hf'
  rw [← not_iff_not]
  simp only [ωSup_le_iff, hf', ωSup, iSup, sSup, mem_range, Chain.map_coe, Function.comp_apply,
    eq_iff_iff, not_forall, OrderHom.coe_mk]
  tauto

theorem continuous_of_scottContinuous {α β} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f : Scott α → Scott β)
    (hf : OmegaCompletePartialOrder.Continuous' f) : Continuous f := by
  rw [continuous_def]
  intro s hs
  change Continuous' (s ∘ f)
  cases' hs with hs hs'
  cases' hf with hf hf'
  apply Continuous.of_bundled
  apply continuous_comp _ _ hf' hs'
