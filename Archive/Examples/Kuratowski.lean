/-
Copyright (c) 2025 Jan Förster, Leon Müller, Luis Sand, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Förster, Leon Müller, Luis Sand, Junyan Xu
-/
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Instances.Real.Lemmas
import Archive.Kuratowski

/-!
# Kuratowski's closure-complement theorem is sharp

Kuratowski's closure-complement theorem says that if one repeatedly applies the closure and
complement operators to a set in a topological space, at most 14 distinct sets can be obtained.

This file gives an example of a so-called "14-set" in ℝ, from which exactly 14 distinct sets
can be obtained.

Our strategy is to show there is no duplication within the fourteen sets obtained from this set
`s`: the fourteen sets can be decomposed into six closed sets, six open sets that are the
complements of the closed sets, and `s` and `sᶜ` which are neither closed nor open.
This reduces `14*13/2 = 91` inequalities to check down to `6*5/2 = 15` inequalities.
We'll further show that the 15 inequalities follow from a subset of 6 by algebra.

There are charaterizations and criteria for a set to be a 14-set in the paper
"Characterization of Kuratowski 14-Sets" by Eric Langford which we do not formalize.

## Main definitions

* `Topology.ClosureCompl.fourteenSet`: an explicit example of a 14-set in ℝ.
* `Topology.ClosureCompl.theClosedSix`: the six open sets obtainable from a given set.
* `Topology.ClosureCompl.theOpenSix`: the six open sets obtainable from a given set.
* `Topology.ClosureCompl.TheSixIneq`: six inequalities that suffice to deduce
  that the six closed sets obtained from a given set contain no duplicates.

## Main results

* `Topology.ClosureCompl.nodup_theFourteen_fourteenSet`:
  the application of all 14 operations on the defined `fourteenSet` in ℝ gives no duplicates.

* `Topology.ClosureCompl.ncard_isObtainable_fourteenSet`:
  for the defined `fourteenSet` in ℝ, there are exactly 14 distinct sets that can be obtained from
  `fourteenSet` using the closure and complement operations.
-/

namespace Topology.ClosureCompl

variable {X : Type*} [TopologicalSpace X] {s t : Set X}


/-- The six closed sets obtained from a given set `s` are given by applying
`k, kc, kck, kckc, kckck, kckckc` to `s`. -/
def theClosedSix (s : Set X) : Multiset (Set X) :=
  {k s, k sᶜ, k (k s)ᶜ, k (k sᶜ)ᶜ, k (k (k s)ᶜ)ᶜ, k (k (k sᶜ)ᶜ)ᶜ}

/-- The complements of the six closed sets. -/
def theOpenSix (s : Set X) : Multiset (Set X) :=
  (theClosedSix s).map compl

/- By applying the identity and complement operations to the six closed sets, we obtain
precisely the six closed sets plus the six open sets. -/
theorem sum_map_theClosedSix_add_compl (s : Set X) :
    ((theClosedSix s).map fun t ↦ {t} + {tᶜ}).sum = theClosedSix s + theOpenSix s :=
  Multiset.sum_map_add

/-- `theFourteen s` can be splitted into 3 subsets. -/
theorem theFourteen_eq_pair_add_theClosedSix_add_theOpenSix (s : Set X) :
    theFourteen s = {s, sᶜ} + theClosedSix s + theOpenSix s := by
  rw [add_assoc, ← sum_map_theClosedSix_add_compl]; rfl

/-- Every set in `theClosedSix s` is closed (because the last operation is closure). -/
theorem isClosed_of_mem_theClosedSix (h : t ∈ theClosedSix s) : IsClosed t := by
  repeat obtain _ | ⟨_, h⟩ := h; rotate_left
  all_goals exact isClosed_closure

/-- Every set in `theOpenSix s` is open. -/
theorem isOpen_of_mem_theOpenSix (h : t ∈ theOpenSix s) : IsOpen t := by
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp h
  exact (isClosed_of_mem_theClosedSix ht).isOpen_compl

theorem mem_theOpenSix_iff : t ∈ theOpenSix s ↔ tᶜ ∈ theClosedSix s := by
  conv_lhs => rw [theOpenSix, ← compl_compl t, Multiset.mem_map_of_injective compl_injective]

/-- Six inequalities that suffice to deduce the six closed sets obtained from a given set
contain no duplicates. -/
def TheSixIneq (s : Set X) : Prop :=
    k (k (k sᶜ)ᶜ)ᶜ ≠ k (k (k s)ᶜ)ᶜ
  ∧ k (k (k sᶜ)ᶜ)ᶜ ≠ k (k sᶜ)ᶜ
  ∧ k (k (k sᶜ)ᶜ)ᶜ ≠ k (k s)ᶜ
  ∧ k (k (k sᶜ)ᶜ)ᶜ ≠ k sᶜ
  ∧ k (k (k s)ᶜ)ᶜ  ≠ k (k s)ᶜ
  ∧ k (k (k s)ᶜ)ᶜ  ≠ k s

open Multiset in
/-- `theClosedSix` applied to an arbitrary set `s` results in no duplicates iff `TheSixIneq`
is true for `s`. -/
theorem nodup_theClosedSix_theFourteen_iff : (theClosedSix s).Nodup ↔ TheSixIneq s := by
  rw [TheSixIneq, theClosedSix]
  simp only [insert_eq_cons, nodup_cons, mem_cons, mem_singleton,
             not_or, nodup_singleton, and_true, ← ne_eq, and_assoc]
  -- The goal becomes 6 inequalities ↔ 15 inequalities.
  constructor -- Show both implications.
  · -- One implication is almost trivial as the six inequalities are among the fifteen.
    tauto
  · intro h -- Introduce `TheSixIneq` as an assumption.
    repeat obtain ⟨_, h⟩ := h -- Split the hypothesis into six different inequalities.
    repeat refine .symm (.intro ?_ ?_) -- Split the goal into 15 inequalities.
    any_goals
      rw [ne_comm]
      try assumption
    -- Solve trivial goals (the six inequalities contained in `TheSixIneq`).
    any_goals
    /- Now eight other goals can be solved by simplifying
      and then using one of the six given inequalities. -/
      apply mt (congr_arg (k ·ᶜ))
      first
      | try repeat rw [kckckck_eq_kck, eq_comm]
        assumption
      | apply mt (congr_arg (k ·ᶜ))
        try repeat rw [kckckck_eq_kck, eq_comm]
        assumption
    -- One last goal (`k (k (k sᶜ)ᶜ)ᶜ ≠ k s`) needs some other simplifying steps:
    · apply mt (congr_arg fun s ↦ k (k sᶜ)ᶜ)
      rw [kckckck_eq_kck]
      assumption

open Multiset in
/-- `theFourteen s` contains no duplicates if and only if `theClosedSix s` has none,
and `theClosedSix s` is disjoint from `theOpenSix s`. -/
theorem nodup_theFourteen_of_nodup_theClosedSix_of_disjoint
    (nodup : (theClosedSix s).Nodup) (disj : Disjoint (theClosedSix s) (theOpenSix s)) :
    (theFourteen s).Nodup := by
  rw [theFourteen_eq_pair_add_theClosedSix_add_theOpenSix, add_assoc, nodup_add, nodup_add]
  refine ⟨?_, ⟨nodup, nodup.map compl_injective, disj⟩, ?_⟩
  -- The two goals now are {s, sᶜ}.Nodup and Disjoint {s, sᶜ} (theClosedSix s + theOpenSix s).
  · -- The first follows from nontriviality of the topological space.
    have : Nontrivial (Set X) := ⟨_, _, (List.pairwise_cons.mp nodup).1 _ (.head _)⟩
    simp
  have hs : ¬ IsClosed s := fun h ↦ by simp [theClosedSix] at nodup
  have hsc : ¬ IsClosed sᶜ := fun h ↦ by simp [theClosedSix] at nodup
  -- Show `s ∉ theClosedSix s ∧ sᶜ ∉ theClosedSix s` and `s ∉ theOpenSix s ∧ sᶜ ∉ theOpenSix s`.
  simp only [insert_eq_cons, disjoint_add_right, disjoint_cons_left, singleton_disjoint,
    mem_theOpenSix_iff, compl_compl, and_comm, and_self]
  exact ⟨(hs <| isClosed_of_mem_theClosedSix ·), (hsc <| isClosed_of_mem_theClosedSix ·)⟩

open Set

/-- A set in `ℝ` from which the maximum of 14 distinct sets can be obtained. -/
def fourteenSet : Set ℝ := Ioo 0 1 ∪ Ioo 1 2 ∪ {3} ∪ (Icc 4 5 ∩ range Rat.cast)

/-!
Let the fourteenSet be s: `(0,1) ∪ (1,2) ∪ {3} ∪ ([4,5] ∩ ℚ)`
Then the following sets can be obtained via the closure and complement operations:
* `cs = (-∞,0] ∪ {1} ∪ [2,3) ∪ (3,4) ∪ ([4,5] \ ℚ) ∪ (5,∞)`
* `kcs = (-∞,0] ∪ {1} ∪ [2,∞)`
* `ckcs = (0,1) ∪ (1,2)`
* `kckcs = [0,2]`
* `ckckcs = (-∞,0) ∪ (2,∞)`
* `kckckcs = (-∞,0] ∪ [2,∞)`
* `ckckckcs = (0,2)`
* `ks = [0,2] ∪ {3} ∪ [4,5]`
* `cks = (-∞,0) ∪ (2,3) ∪ (3,4) ∪ (5,∞)`
* `kcks = (-∞,0] ∪ [2,4] ∪ [5,∞)`
* `ckcks = (0,2) ∪ (4,5)`
* `kckcks = [0,2] ∪ [4,5]`
* `ckckcks = (-∞,0) ∪ (2,4) ∪ (5,∞)`

We can see that the sets are pairwise distinct, so we have 14 distinct sets.
-/

theorem k_Icc_4_5_inter_rat : k (Icc (4 : ℝ) 5 ∩ range Rat.cast) = Icc 4 5 :=
  (closure_ordConnected_inter_rat ordConnected_Icc ⟨4, by norm_num, 5, by norm_num⟩).trans
    isClosed_Icc.closure_eq

theorem i_fourteenSet : i fourteenSet = Ioo 0 1 ∪ Ioo 1 2 := by
  have := interior_eq_empty_iff_dense_compl.mpr dense_irrational
  rw [fourteenSet, interior_union_of_disjoint_closure, interior_union_of_disjoint_closure]
  · simp [(isOpen_Ioo.union isOpen_Ioo).interior_eq, this]
  all_goals norm_num [-union_singleton, k_Icc_4_5_inter_rat,
    disjoint_iff_inter_eq_empty, union_inter_distrib_right, Icc_inter_Icc]

theorem k_fourteenSet : k fourteenSet = Icc 0 2 ∪ {3} ∪ Icc 4 5 := by
  simp_rw [fourteenSet, closure_union]
  rw [closure_Ioo, closure_Ioo, k_Icc_4_5_inter_rat, Icc_union_Icc']
  all_goals norm_num

theorem kc_fourteenSet : k fourteenSetᶜ = (Ioo 0 1 ∪ Ioo 1 2)ᶜ := by
  rw [closure_compl, compl_inj_iff, i_fourteenSet]

theorem kck_fourteenSet : k (k fourteenSet)ᶜ = (Ioo 0 2 ∪ Ioo 4 5)ᶜ := by
  rw [closure_compl, k_fourteenSet,
    interior_union_of_disjoint_closure, interior_union_of_disjoint_closure]
  all_goals norm_num
    [-union_singleton, disjoint_iff_inter_eq_empty, union_inter_distrib_right, Icc_inter_Icc]

theorem kckc_fourteenSet : k (k fourteenSetᶜ)ᶜ = Icc 0 2 := by
  rw [kc_fourteenSet, compl_compl, closure_union, closure_Ioo, closure_Ioo]
  all_goals norm_num

theorem kckck_fourteenSet : k (k (k fourteenSet)ᶜ)ᶜ = Icc 0 2 ∪ Icc 4 5 := by
  rw [kck_fourteenSet, compl_compl, closure_union, closure_Ioo, closure_Ioo]
  all_goals norm_num

theorem kckckc_fourteenSet : k (k (k fourteenSetᶜ)ᶜ)ᶜ = (Ioo 0 2)ᶜ := by
  rw [kckc_fourteenSet, closure_compl, interior_Icc]

/-- `theClosedSix` applied to the specific `fourteenSet` generates no duplicates. -/
theorem nodup_theClosedSix_fourteenSet : (theClosedSix fourteenSet).Nodup := by
  rw [nodup_theClosedSix_theFourteen_iff, TheSixIneq, kckckc_fourteenSet, kckck_fourteenSet,
    kckc_fourteenSet, kck_fourteenSet, kc_fourteenSet, k_fourteenSet]
  refine ⟨(ne_of_mem_of_not_mem' (a := 1) ?_ ?_).symm,
    (ne_of_mem_of_not_mem' (a := 1) ?_ ?_).symm,
    ne_of_mem_of_not_mem' (a := 4.5) ?_ ?_,
    (ne_of_mem_of_not_mem' (a := 1) ?_ ?_).symm,
    ne_of_mem_of_not_mem' (a := 1) ?_ ?_,
    (ne_of_mem_of_not_mem' (a := 3) ?_ ?_).symm⟩
  all_goals norm_num

/-- No set from `theClosedSix fourteenSet` is empty. -/
theorem nonempty_of_mem_theClosedSix_fourteenSet {s}
    (h : s ∈ theClosedSix fourteenSet) : s.Nonempty := by
  rw [theClosedSix, kckckc_fourteenSet, kckck_fourteenSet,
    kckc_fourteenSet, kck_fourteenSet, kc_fourteenSet, k_fourteenSet] at h
  repeat obtain _ | ⟨_, h⟩ := h; rotate_left
  all_goals use 2; norm_num

/-- No set from `theClosedSix fourteenSet` is the universal set. -/
theorem not_eq_univ_of_mem_theClosedSix_fourteenSet {s}
    (h : s ∈ theClosedSix fourteenSet) : s ≠ univ := by
  rw [theClosedSix, kckckc_fourteenSet, kckck_fourteenSet,
    kckc_fourteenSet, kck_fourteenSet, kc_fourteenSet, k_fourteenSet] at h
  rw [Ne, eq_univ_iff_forall]
  push_neg
  repeat obtain _ | ⟨_, h⟩ := h; rotate_left
  · use 1/2; norm_num
  · use 1/2; norm_num
  · use 6;   norm_num
  · use 6;   norm_num
  · use 1/2; norm_num
  · use 6;   norm_num

/-- The fourteen different operations applied to the `fourteenSet` generate no duplicates. -/
theorem nodup_theFourteen_fourteenSet : (theFourteen fourteenSet).Nodup :=
  nodup_theFourteen_of_nodup_theClosedSix_of_disjoint nodup_theClosedSix_fourteenSet <|
    Multiset.disjoint_iff_ne.mpr <| by
      rintro s hc _ ho rfl
      exact not_eq_univ_of_mem_theClosedSix_fourteenSet hc <| IsClopen.eq_univ
        ⟨isClosed_of_mem_theClosedSix hc, isOpen_of_mem_theOpenSix ho⟩
        (nonempty_of_mem_theClosedSix_fourteenSet hc)

/-- The number of distinct sets obtainable from `fourteenSet` is exactly 14. -/
theorem ncard_isObtainable_fourteenSet : {t | IsObtainable fourteenSet t}.ncard = 14 := by
  classical rw [← card_theFourteen fourteenSet, ← Multiset.toFinset_card_of_nodup
    nodup_theFourteen_fourteenSet, ← Set.ncard_coe_finset]
  congr; ext; simp [mem_theFourteen_iff_isObtainable]

end Topology.ClosureCompl
