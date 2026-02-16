/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs

import Mathlib.Data.Set.Lattice

/-! # Basic results on conditionally complete partial orders

This file contains some basic results on conditionally complete partial orders, and is intended
to parallel the API for conditionally complete lattices where possible. For the reason, the
theorems here are mostly protected within the `DirectedOn` namespace, unless such an assumption is
unnecessary. Otherwise the names here share the same names as their counterparts in
`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`.

-/
@[expose] public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

namespace OrderDual

instance [ConditionallyCompletePartialOrderSup α] :
    ConditionallyCompletePartialOrderInf αᵒᵈ where
  isGLB_csInf_of_directed _ h_dir h_non h_bdd := h_dir.isLUB_csSup (α := α) h_non h_bdd

instance [ConditionallyCompletePartialOrderInf α] :
    ConditionallyCompletePartialOrderSup αᵒᵈ where
  isLUB_csSup_of_directed _ h_dir h_non h_bdd := h_dir.isGLB_csInf (α := α) h_non h_bdd

instance [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder αᵒᵈ where

end OrderDual

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {s t : Set α} {a b : α}

@[to_dual csInf_le_of_le]
protected theorem DirectedOn.le_csSup_of_le (hd : DirectedOn (· ≤ ·) s)
    (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (hd.le_csSup hs hb)

@[to_dual (attr := gcongr low)]
protected theorem DirectedOn.csSup_le_csSup (hds : DirectedOn (· ≤ ·) s)
    (hdt : DirectedOn (· ≤ ·) t) (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) :
    sSup s ≤ sSup t :=
  hds.csSup_le hs fun _ ha => hdt.le_csSup ht (h ha)

@[to_dual csInf_le_iff]
protected theorem DirectedOn.le_csSup_iff (hd : DirectedOn (· ≤ ·) s) (h : BddAbove s)
    (hs : s.Nonempty) : a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (hd.csSup_le hs hb), fun hb => hb _ fun _ => hd.le_csSup h⟩

@[to_dual]
theorem IsGreatest.directedOn (H : IsGreatest s a) : DirectedOn (· ≤ ·) s :=
  fun _ h₁ _ h₂ ↦ ⟨a, H.1, H.2 h₁, H.2 h₂⟩

/-- A greatest element of a set is the supremum of this set. -/
@[to_dual /-- A least element of a set is the infimum of this set. -/]
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.directedOn.isLUB_csSup H.nonempty ⟨a, H.2⟩ |>.unique H.isLUB

@[to_dual]
theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1

@[to_dual le_csInf_iff]
protected theorem DirectedOn.csSup_le_iff (hd : DirectedOn (· ≤ ·) s)
    (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (hd.isLUB_csSup hs hb)

@[to_dual notMem_of_lt_csInf]
protected theorem DirectedOn.notMem_of_csSup_lt {x : α} {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  fun hx ↦ lt_irrefl _ <| (hd.le_csSup hs hx).trans_lt h

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual DirectedOn.csInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/ ]
protected theorem DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (hd : DirectedOn (· ≤ ·) s) (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (hd.csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| hd.le_csSup ⟨b, H⟩ ha

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
@[to_dual DirectedOn.csInf_lt_of_lt
/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/ ]
protected theorem DirectedOn.lt_csSup_of_lt (hd : DirectedOn (· ≤ ·) s) (hs : BddAbove s)
    (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (hd.le_csSup hs ha)

/-- The supremum of a singleton is the element of the singleton -/
@[to_dual (attr := simp)]
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq

@[simp]
theorem csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α] {a : α} :
    sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq

@[simp]
theorem csInf_Ico {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α} (h : a < b) :
    sInf (Ico a b) = a :=
  (isLeast_Ico h).csInf_eq

@[simp]
theorem csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α] {a b : α}
    (h : a ≤ b) : sInf (Icc a b) = a :=
  (isLeast_Icc h).csInf_eq

@[to_dual existing, simp]
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq

@[to_dual existing, simp]
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isGreatest_Ioc h).csSup_eq

@[simp]
theorem csSup_Icc {a b : α} (h : a ≤ b) : sSup (Icc a b) = b :=
  (isGreatest_Icc h).csSup_eq

@[to_dual]
lemma sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ ∈ s) : sSup s = ⊤ :=
  IsGreatest.csSup_eq ⟨h, fun _ _ ↦ le_top⟩

end ConditionallyCompletePartialOrderSup

section ConditionallyCompletePartialOrder

variable [ConditionallyCompletePartialOrder α] {s t : Set α} {a b : α}

protected theorem DirectedOn.subset_Icc_csInf_csSup (hdb : DirectedOn (· ≥ ·) s)
    (hda : DirectedOn (· ≤ ·) s) (hb : BddBelow s) (ha : BddAbove s) :
    s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨hdb.csInf_le hb hx, hda.le_csSup ha hx⟩

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
protected theorem DirectedOn.csInf_le_csSup (hdb : DirectedOn (· ≥ ·) s)
    (hda : DirectedOn (· ≤ ·) s) (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) :
    sInf s ≤ sSup s :=
  isGLB_le_isLUB (hdb.isGLB_csInf ne hb) (hda.isLUB_csSup ne ha) ne

end ConditionallyCompletePartialOrder
