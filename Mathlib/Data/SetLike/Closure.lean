/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Lattice

/-!
# Typeclass for lattices with a closure-adjoint embedding into a power set.

This file defines a typeclass for lattices `L` that embed nicely into a power set `Set α`,
in the sense that the closure operation `Set α → L` is adjoint to the embedding. The main purpose
of this class is to abstract the closure construction common to most algebraic substructures.

## Main definitions

* `LatticeSetLike` : class for complete lattices that have an embedding into some `Set α`
  which preserves arbitrary infima.
* `SetLike.closure` : the natural closure operation on `Set α` with respect to a
  `LatticeSetLike` embedding; that is, the map from a set to the least lattice element that
  contains it.

## Main result

* `SetLike.gi_closure` : for a `LatticeSetLike`, the operations
  `SetLike.closure` and `SetLike.coe` (the embedding) form a Galois insertion.

-/

/-
Typeclass for complete lattices `L` with a canonical order-preserving injection into `Set α`
which preserves the order and arbitrary infima.
-/
class LatticeSetLike (L : Type*) (α : outParam Type*)
    extends CompleteLattice L, OrderedSetLike L α where
  coe_sInf' (s : Set L) : coe (sInf s) = InfSet.sInf (coe '' s)

/- Construct a `LatticeSetLike` from a complete lattice `L` and an injection `L → Set α`
that preserves arbitrary infima. -/
def CompleteLattice.toLatticeSetLike (L α : Type*) [SetLike L α] [CompleteLattice L]
      (coe_sInf : ∀ {s : Set L}, SetLike.coe (sInf s) = ⋂ m ∈ s, m) :
    LatticeSetLike L α where
  coe := SetLike.coe
  coe_sInf' := by simpa
  coe_subset_coe' {l m} := by
    suffices (l : Set α) ⊆ m ↔ (sInf {l, m}) = (l : Set α) by simpa
    rw [coe_sInf]; simp

/- Construct a `LatticeSetLike` from a type `L` and an order-preserving injection `L → Set α`
that preserves arbitrary infima. -/
def OrderedSetLike.toLatticeSetLike (L α : Type*) [OrderedSetLike L α] [InfSet L]
    (coe_sInf : ∀ {s : Set L}, SetLike.coe (sInf s) = ⋂ m ∈ s, m) :
    LatticeSetLike L α where
  __ := ‹OrderedSetLike L α›
  __ := completeLatticeOfInf L fun s =>
      IsGLB.of_image OrderedSetLike.coe_subset_coe (by simpa [coe_sInf] using isGLB_biInf)
  coe_sInf' := by simpa

/- Construct a `LatticeSetLike` from a type `L` and an injection `L → Set α`
that reflects arbitrary intersections. -/
noncomputable def SetLike.toLatticeSetLike (L α : Type*) [SetLike L α]
    (exists_coe_eq_iInter : ∀ {s : Set L}, ∃ l : L, (l : Set α) = ⋂ m ∈ s, m) :
    LatticeSetLike L α :=
  @OrderedSetLike.toLatticeSetLike L α SetLike.toOrderedSetLike
    ⟨fun _ => Classical.choose exists_coe_eq_iInter⟩
    (Classical.choose_spec exists_coe_eq_iInter)

namespace LatticeSetLike

variable {L α : Type*} [LatticeSetLike L α]

@[simp, norm_cast]
theorem coe_sInf {s : Set L} : ((sInf s : L) : Set α) = ⋂ l ∈ s, l := by
  simpa using LatticeSetLike.coe_sInf' s

theorem mem_sInf {s : Set L} {x : α} : x ∈ sInf s ↔ ∀ l ∈ s, x ∈ l := by
  rw [← SetLike.mem_coe]; simp

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {l : ι → L} : (↑(⨅ i, l i) : Set α) = ⋂ i, l i := by simp [iInf]

theorem mem_iInf {ι : Sort*} {l : ι → L} {x : α} : (x ∈ ⨅ i, l i) ↔ ∀ i, x ∈ l i := by
  rw [← SetLike.mem_coe]; simp

@[simp]
theorem coe_top : ((⊤ : L) : Set α) = Set.univ := by
  suffices sInf (∅ : Set L) = (Set.univ : Set α) by simpa only [sInf_empty]
  rw [coe_sInf]; simp

@[simp]
theorem mem_top (x : α) : x ∈ (⊤ : L) := by
  rw [← SetLike.mem_coe]; simp

@[simp]
theorem coe_inf (l m : L) : ((l ⊓ m : L) : Set α) = (l : Set α) ∩ m := by
  suffices sInf {l, m} = (l : Set α) ∩ m by simpa
  rw [coe_sInf]; simp

@[simp]
theorem mem_inf {l m : L} {x : α} : x ∈ l ⊓ m ↔ x ∈ l ∧ x ∈ m := by
  rw [← SetLike.mem_coe]; simp

theorem coe_bot : ((⊥ : L) : Set α) = ⋂ l : L, l := by
  suffices ((sInf (Set.univ) : L) : Set α) = ⋂ l : L, l by simpa
  rw [coe_sInf]; simp

theorem mem_bot {x : α} : x ∈ (⊥ : L) ↔ ∀ l : L, x ∈ l := by
  rw [← SetLike.mem_coe, coe_bot]; simp

/- `closure L s` is the least element of `L` containing `s`. -/
variable (L) in
def closure (s : Set α) : L := sInf { l | s ⊆ l }

theorem coe_closure {s : Set α} : (closure L s : Set α) = ⋂ l ∈ {m : L | s ⊆ m}, l := coe_sInf

theorem mem_closure {s : Set α} {x : α} : x ∈ closure L s ↔ ∀ l : L, s ⊆ l → x ∈ l := mem_sInf

variable (L) in
open LatticeSetLike OrderedSetLike in
def gi_closure : GaloisInsertion (closure L) SetLike.coe :=
  GaloisConnection.toGaloisInsertion
    (fun _ _ =>
      ⟨fun h => Set.Subset.trans (fun _ hx => mem_closure.2 fun _ hs => hs hx) (mem_of_le_of_mem h),
      (sInf_le ·)⟩)
    fun _ => le_sInf (fun _ => coe_subset_coe.1)

@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set α} : s ⊆ closure L s := (gi_closure L).gc.le_u_l s

@[aesop unsafe 50% apply (rule_sets := [SetLike])]
theorem mem_closure_of_mem {s : Set α} {x : α} (hx : x ∈ s) : x ∈ closure L s := subset_closure hx

theorem not_mem_of_not_mem_closure {s : Set α} {x : α} (hx : x ∉ closure L s) : x ∉ s :=
  (hx <| subset_closure ·)

@[simp]
theorem closure_le {s : Set α} {l : L} : closure L s ≤ l ↔ s ⊆ l := (gi_closure L).gc.le_iff_le

theorem closure_monotone : Monotone (closure L : Set α → L) := (gi_closure L).gc.monotone_l

@[gcongr]
theorem closure_mono ⦃s t : Set α⦄ (h : s ⊆ t) : closure L s ≤ closure L t := closure_monotone h

theorem closure_eq_of_le {s : Set α} {l : L} (h₁ : s ⊆ l) (h₂ : l ≤ closure L s) :
    closure L s = l := le_antisymm (closure_le.2 h₁) h₂

@[simp] theorem closure_eq (l : L) : closure L (l : Set α) = l := (gi_closure L).l_u_eq l

@[simp] theorem closure_empty : closure L (∅ : Set α) = ⊥ := (gi_closure L).gc.l_bot

@[simp] theorem closure_univ : closure L (Set.univ : Set α) = ⊤ := (gi_closure L).l_top

theorem closure_union (s t : Set α) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
  (gi_closure L).gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set α) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (gi_closure L).gc.l_iSup

theorem closure_singleton_le_iff_mem (x : α) (l : L) : closure L {x} ≤ l ↔ x ∈ l := by
  rw [closure_le, Set.singleton_subset_iff, SetLike.mem_coe]

theorem mem_iSup {ι : Sort*} (l : ι → L) {x : α} :
    (x ∈ ⨆ i, l i) ↔ ∀ m, (∀ i, l i ≤ m) → x ∈ m := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

theorem iSup_eq_closure {ι : Sort*} (l : ι → L) :
    ⨆ i, l i = closure L (⋃ i, (l i : Set α)) := by
  simp_rw [closure_iUnion, closure_eq]

end LatticeSetLike
