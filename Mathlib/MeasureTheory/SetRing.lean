/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.SetSemiring

/-! # Rings of sets

A ring of sets `C` (in the sense of measure theory) is a family of sets containing `∅`,
stable by union and set-differences. Using `s ∩ t = s \ (t \ s)`, it is also stable under
intersection. Note that a ring of sets may not contain `univ`.

Typically, rings arise by taking unions of sets in a semi-ring (e.g. the set of intervals).

## Main definitions

* `MeasureTheory.IsSetRing`: property of being a ring of sets.

## Main statements

* `MeasureTheory.IsSetRing.inter_mem`: a ring is stsable under intersections.

TODO: State the result that finite unions of sets in a semi-ring form a ring.

-/

open Finset Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/-- A ring of sets `C` is a family of sets containing `∅`, stable by union and set difference.
It is then also stable by intersection (see `IsSetRing.inter_mem`). -/
structure IsSetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ C
  union_mem ⦃s t⦄ : s ∈ C → t ∈ C → s ∪ t ∈ C
  diff_mem ⦃s t⦄ : s ∈ C → t ∈ C → s \ t ∈ C

namespace IsSetRing

lemma inter_mem (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) : s ∩ t ∈ C := by
  rw [← diff_diff_right_self]; exact hC.diff_mem hs (hC.diff_mem hs ht)

/-- A ring is a semi-ring. -/
lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  diff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.diff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]

lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋃ i ∈ S, s i ∈ C := by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | @insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS ↦ hs n (mem_insert_of_mem hnS))

lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : ∀ n ∈ S, s n ∈ C) :
    ⋂ i ∈ S, s i ∈ C := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS ↦ hs.2 n hnS)

lemma finsetSup_mem (hC : IsSetRing C) {ι : Type*} {s : ι → Set α} {t : Finset ι}
    (hs : ∀ i ∈ t, s i ∈ C) :
    t.sup s ∈ C := by
  classical
  induction t using Finset.induction_on with
  | empty => exact hC.empty_mem
  | @insert m t hm ih =>
    simpa only [sup_insert] using
      hC.union_mem (hs m <| mem_insert_self m t) (ih <| fun i hi ↦ hs _ <| mem_insert_of_mem hi)

lemma partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ n, s n ∈ C) (n : ι) :
    partialSups s n ∈ C := by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi ↦ hs i)

lemma disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι → Set α} (hs : ∀ j, s j ∈ C) (i : ι) :
    disjointed s i ∈ C :=
  disjointedRec (fun _ j ht ↦ hC.diff_mem ht <| hs j) (hs i)

theorem iUnion_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)

theorem iInter_le_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ n, s n ∈ C) (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)

theorem accumulate_mem (hC : IsSetRing C) {s : ℕ → Set α} (hs : ∀ i, s i ∈ C) (n : ℕ) :
    Accumulate s n ∈ C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

end IsSetRing

end MeasureTheory
