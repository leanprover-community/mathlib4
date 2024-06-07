/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Pairwise

#align_import data.finsupp.big_operators from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!

# Sums of collections of Finsupp, and their support
This file provides results about the `Finsupp.support` of sums of collections of `Finsupp`,
including sums of `List`, `Multiset`, and `Finset`.

The support of the sum is a subset of the union of the supports:
* `List.support_sum_subset`
* `Multiset.support_sum_subset`
* `Finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `List.support_sum_eq`
* `Multiset.support_sum_eq`
* `Finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `List.mem_foldr_sup_support_iff`
* `Multiset.mem_sup_map_support_iff`
* `Finset.mem_sup_support_iff`

-/


variable {ι M : Type*} [DecidableEq ι]

theorem List.support_sum_subset [AddMonoid M] (l : List (ι →₀ M)) :
    l.sum.support ⊆ l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction' l with hd tl IH
  · simp
  · simp only [List.sum_cons, Finset.union_comm]
    refine Finsupp.support_add.trans (Finset.union_subset_union ?_ IH)
    rfl
#align list.support_sum_subset List.support_sum_subset

theorem Multiset.support_sum_subset [AddCommMonoid M] (s : Multiset (ι →₀ M)) :
    s.sum.support ⊆ (s.map Finsupp.support).sup := by
  induction s using Quot.inductionOn
  simpa only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe, Multiset.sup_coe,
    List.foldr_map] using List.support_sum_subset _
#align multiset.support_sum_subset Multiset.support_sum_subset

theorem Finset.support_sum_subset [AddCommMonoid M] (s : Finset (ι →₀ M)) :
    (s.sum id).support ⊆ Finset.sup s Finsupp.support := by
  classical convert Multiset.support_sum_subset s.1; simp
#align finset.support_sum_subset Finset.support_sum_subset

theorem List.mem_foldr_sup_support_iff [Zero M] {l : List (ι →₀ M)} {x : ι} :
    x ∈ l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ ∃ f ∈ l, x ∈ f.support := by
  simp only [Finset.sup_eq_union, List.foldr_map, Finsupp.mem_support_iff, exists_prop]
  induction' l with hd tl IH
  · simp
  · simp only [foldr, Function.comp_apply, Finset.mem_union, Finsupp.mem_support_iff, ne_eq, IH,
      find?, mem_cons, exists_eq_or_imp]
#align list.mem_foldr_sup_support_iff List.mem_foldr_sup_support_iff

theorem Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι →₀ M)} {x : ι} :
    x ∈ (s.map Finsupp.support).sup ↔ ∃ f ∈ s, x ∈ f.support :=
  Quot.inductionOn s fun _ ↦ by
    simpa only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
    using List.mem_foldr_sup_support_iff
#align multiset.mem_sup_map_support_iff Multiset.mem_sup_map_support_iff

theorem Finset.mem_sup_support_iff [Zero M] {s : Finset (ι →₀ M)} {x : ι} :
    x ∈ s.sup Finsupp.support ↔ ∃ f ∈ s, x ∈ f.support :=
  Multiset.mem_sup_map_support_iff
#align finset.mem_sup_support_iff Finset.mem_sup_support_iff

theorem List.support_sum_eq [AddMonoid M] (l : List (ι →₀ M))
    (hl : l.Pairwise (_root_.Disjoint on Finsupp.support)) :
    l.sum.support = l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction' l with hd tl IH
  · simp
  · simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons, Function.comp_apply]
    rw [Finsupp.support_add_eq, IH hl.right, Finset.sup_eq_union]
    suffices _root_.Disjoint hd.support (tl.foldr (fun x y ↦ (Finsupp.support x ⊔ y)) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    rw [← List.foldr_map, ← Finset.bot_eq_empty, List.foldr_sup_eq_sup_toFinset,
      Finset.disjoint_sup_right]
    intro f hf
    simp only [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    exact hl.left _ hf
#align list.support_sum_eq List.support_sum_eq

theorem Multiset.support_sum_eq [AddCommMonoid M] (s : Multiset (ι →₀ M))
    (hs : s.Pairwise (_root_.Disjoint on Finsupp.support)) :
    s.sum.support = (s.map Finsupp.support).sup := by
  induction' s using Quot.inductionOn with a
  obtain ⟨l, hl, hd⟩ := hs
  suffices a.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert List.support_sum_eq a this
    · simp only [Multiset.quot_mk_to_coe'', Multiset.sum_coe]
    · dsimp only [Function.comp_def]
      simp only [quot_mk_to_coe'', map_coe, sup_coe, ge_iff_le, Finset.le_eq_subset,
        Finset.sup_eq_union, Finset.bot_eq_empty, List.foldr_map]
  simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.coe_eq_coe] at hl
  exact hl.symm.pairwise hd fun h ↦ _root_.Disjoint.symm h
#align multiset.support_sum_eq Multiset.support_sum_eq

theorem Finset.support_sum_eq [AddCommMonoid M] (s : Finset (ι →₀ M))
    (hs : (s : Set (ι →₀ M)).PairwiseDisjoint Finsupp.support) :
    (s.sum id).support = Finset.sup s Finsupp.support := by
  classical
  suffices s.1.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert Multiset.support_sum_eq s.1 this
    exact (Finset.sum_val _).symm
  obtain ⟨l, hl, hn⟩ : ∃ l : List (ι →₀ M), l.toFinset = s ∧ l.Nodup := by
    refine ⟨s.toList, ?_, Finset.nodup_toList _⟩
    simp
  subst hl
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise, ←
    List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]
  intro x y hxy
  exact symmetric_disjoint hxy
#align finset.support_sum_eq Finset.support_sum_eq
