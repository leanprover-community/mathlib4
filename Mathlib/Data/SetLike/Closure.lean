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

* `SetLikeCompleteLattice` : class for complete lattices that have an embedding into some `Set α`
  which preserves the order and arbitrary infima.
* `SetLike.closure` : the natural closure operation on `Set α` with respect to a
  `SetLikeCompleteLattice` embedding; that is, the map from a set to the least lattice element that
  contains it.

## Main result

* `SetLike.gi_closure` : for a `SetLikeCompleteLattice`, the operations
  `SetLike.closure` and `SetLike.coe` (the embedding) form a Galois insertion.

-/

class SetLikeCompleteLattice (L α : Type*) extends CompleteLattice L, SetLike L α where
  le_def' : le =
    @LE.le L (@Preorder.toLE L (@PartialOrder.toPreorder L SetLike.instPartialOrder))
  lt_def' : lt =
    @LT.lt L (@Preorder.toLT L (@PartialOrder.toPreorder L SetLike.instPartialOrder))
  coe_sInf' (s : Set L) : sInf s = InfSet.sInf (SetLike.coe '' s)

namespace SetLike

variable {α L : Type*} [SetLikeCompleteLattice L α]

@[simp, norm_cast]
protected theorem coe_sInf (s : Set L) : ((sInf s : L) : Set α) = ⋂ a ∈ s, ↑a := by
  simpa using SetLikeCompleteLattice.coe_sInf' s

protected theorem mem_sInf {s : Set L} {x : α} : x ∈ sInf s ↔ ∀ a ∈ s, x ∈ a := by
  rw [← SetLike.mem_coe]; simp

variable (L) in
def closure (s : Set α) : L := sInf { l | s ⊆ l }

theorem mem_closure {s : Set α} {x : α} : x ∈ closure L s ↔ ∀ l : L, s ⊆ l → x ∈ l :=
  SetLike.mem_sInf

variable (L) in
open SetLikeCompleteLattice in
def gi_closure : GaloisInsertion (closure L) SetLike.coe :=
  GaloisConnection.toGaloisInsertion
    (fun _ _ =>
      ⟨by rw [le_def']; exact Set.Subset.trans <| fun _ hx => mem_closure.2 fun _ hs => hs hx,
      fun h => sInf_le h⟩)
    fun _ => by rw [le_def']; exact fun _ hx => mem_closure.2 fun _ hs => hs hx

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

end SetLike
