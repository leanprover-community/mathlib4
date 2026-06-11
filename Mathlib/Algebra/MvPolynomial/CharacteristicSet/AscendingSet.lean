/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.PseudoDivision

/-!
# Ascending sets and basic sets

This file defines the abstract theory of **ascending sets** and **basic sets**.
An ascending set is a triangular set with additional reduction properties.
A basic set is the "smallest" ascending set contained in a given set of polynomials.

## Main declarations

* `AscendingSetTheory`: A typeclass abstracting the definition of an ascending set
  (e.g., strong vs. weak reduction).
* `AscendingSetTheory`: A typeclass abstracting the definition of an ascending set
  (e.g., strong vs. weak reduction) and the algorithm to compute a basic set.
  from a list of polynomials.

-/

@[expose] public section

open MvPolynomial

/--
The abstract theory of Ascending Sets.
This class allows us to define what it means for a `TriangularSet` to be an "Ascending Set".
Different instances can implement Ritt's strong ascending sets or Wu's weak ascending sets.
-/
class AscendingSetTheory (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ]
    (isAscendingSet : TriangularSet σ R → Prop) where
  decidableReducedTo : DecidablePred isAscendingSet := by infer_instance
  /-- A key property linking the ascending set structure to the initial.
  If `S` is an ascending set, the initial of any non-constant element in `S`
  must be reduced with respect to `S`. -/
  initial_reducedToSet_of_max_vars_ne_bot : ∀ ⦃S : TriangularSet σ R⦄ ⦃i : ℕ⦄,
    isAscendingSet S → (S i).vars.max ≠ ⊥ → (S i).initial.reducedToSet S
  /-- Computes a Basic Set from a list of polynomials. -/
  basicSet : List (MvPolynomial σ R) → TriangularSet σ R
  /-- The output is always an Ascending Set. -/
  basicSet_isAscendingSet (l : List (MvPolynomial σ R)) : isAscendingSet (basicSet l)
  /-- The output is a subset of the input. -/
  basicSet_subset (l : List (MvPolynomial σ R)) : ∀ ⦃c⦄, c ∈ basicSet l → c ∈ l
  /-- Minimality condition: the output is ≤ any other ascending set contained in the input. -/
  basicSet_minimal (l : List (MvPolynomial σ R)) :
      ∀ ⦃S⦄, isAscendingSet S → (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S
  /-- Order reduction property: appending a reduced element strictly decreases the basic set order.
  Crucial for proving termination of zero decomposition. -/
  basicSet_append_lt_of_exists_reducedToSet : ∀ ⦃l1 l2 : List (MvPolynomial σ R)⦄,
      (∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (basicSet l1)) → basicSet (l2 ++ l1) < basicSet l1

attribute [instance_reducible, instance 900] AscendingSetTheory.decidableReducedTo

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ] [DecidableEq R]

namespace TriangularSet

/-- Definition of Standard (Ritt) Ascending Set: A Triangular Set is an Ascending Set
if every element is reduced with respect to its predecessors. -/
def IsAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).reducedTo (S i)

/-- Definition of Weak (Wu) Ascending Set: A Triangular Set is an Ascending Set
if every element's initial is reduced with respect to its predecessors. -/
def IsWeakAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).initial.reducedTo (S i)

theorem isAscendingSet_iff {S : TriangularSet σ R} : S.IsAscendingSet ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rw [eq_zero_iff_length_le.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

theorem isWeakAscendingSet_iff {S : TriangularSet σ R} : S.IsWeakAscendingSet ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).initial.reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rw [eq_zero_iff_length_le.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

noncomputable instance : @DecidablePred (TriangularSet σ R) IsAscendingSet := fun _ ↦
  have {S : TriangularSet σ R} :
      (∀ j < S.length, ∀ i < j, (S j).reducedTo (S i)) ↔ S.IsAscendingSet :=
    ⟨fun h i j hi hj ↦ h j hj i hi, fun h _ hj _ hi ↦ h hi hj⟩
  decidable_of_iff _ this

noncomputable instance : @DecidablePred (TriangularSet σ R) IsWeakAscendingSet := fun _ ↦
  have {S : TriangularSet σ R} :
      (∀ j < S.length, ∀ i < j, (S j).initial.reducedTo (S i)) ↔ S.IsWeakAscendingSet :=
    ⟨fun h i j hi hj ↦ h j hj i hi, fun h _ hj _ hi ↦ h hi hj⟩
  decidable_of_iff _ this

theorem isWeakAscendingSet_of_isAscendingSet {S : TriangularSet σ R} :
    IsAscendingSet S → IsWeakAscendingSet S :=  fun h _ _ hij hj ↦ initial_reducedTo (h hij hj)

theorem initial_reducedToSet_of_max_vars_ne_bot
    {isAscendingSet : TriangularSet σ R → Prop} [AscendingSetTheory σ R isAscendingSet]
    {S : TriangularSet σ R} {i : ℕ} :
    isAscendingSet S → (S i).vars.max ≠ ⊥ → (S i).initial.reducedToSet S :=
  fun h1 h2 ↦ AscendingSetTheory.initial_reducedToSet_of_max_vars_ne_bot h1 h2

theorem initial_reducedToSet_of_max_vars_ne_bot'
    {isAscendingSet : TriangularSet σ R → Prop} [AscendingSetTheory σ R isAscendingSet]
    {S : TriangularSet σ R} {p : MvPolynomial σ R} (h : isAscendingSet S) :
    p ∈ S → p.vars.max ≠ ⊥ → p.initial.reducedToSet S := fun ⟨_, _, hi2⟩ hc ↦
  hi2 ▸ initial_reducedToSet_of_max_vars_ne_bot h (hi2 ▸ hc)

theorem isAscendingSet_single (p : MvPolynomial σ R) : (single p).IsAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isAscendingSet_empty : (∅ : TriangularSet σ R).IsAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : MvPolynomial σ R) = ∅) ▸ isAscendingSet_single 0

variable {S : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isAscendingSet_take (n : ℕ) :
    S.IsAscendingSet → (S.take n).IsAscendingSet := fun hs i j hij hj ↦ by
  rw [S.length_take] at hj
  rw [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isAscendingSet_drop (n : ℕ) : S.IsAscendingSet → (S.drop n).IsAscendingSet := by
  intro hs a b hij hj
  rw [drop_apply, drop_apply]
  exact hs (Nat.add_lt_add_left hij n) (Nat.add_lt_of_lt_sub' (S.length_drop _ ▸ hj))

theorem isAscendingSet_concat (h : S.CanConcat p) (hp : p.reducedToSet S) :
    S.IsAscendingSet → (S.concat p).IsAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_add_one (S.length_concat h ▸ hj)
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rw [if_pos hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp _ <| apply_mem hi

theorem isAscendingSet_takeConcat (hp : p.reducedToSet S) :
    S.IsAscendingSet → (S.takeConcat p).IsAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isAscendingSet_single p
  refine TriangularSet.isAscendingSet_concat _ (fun n hn ↦ ?_) <| isAscendingSet_take _ h
  apply hp
  exact TriangularSet.take_subset S _ <| mem_def.mpr hn

theorem isWeakAscendingSet_single (p : MvPolynomial σ R) : (single p).IsWeakAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isWeakAscendingSet_empty : (∅ : TriangularSet σ R).IsWeakAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : MvPolynomial σ R) = ∅) ▸ isWeakAscendingSet_single 0

variable {S : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isWeakAscendingSet_take (n : ℕ) :
    S.IsWeakAscendingSet → (S.take n).IsWeakAscendingSet := fun hs i j hij hj ↦ by
  rw [S.length_take] at hj
  rw [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isWeakAscendingSet_drop (n : ℕ) : S.IsWeakAscendingSet → (S.drop n).IsWeakAscendingSet := by
  intro hs a b hij hj
  rw [drop_apply, drop_apply]
  exact hs (Nat.add_lt_add_left hij n) (Nat.add_lt_of_lt_sub' (S.length_drop _ ▸ hj))

theorem isWeakAscendingSet_concat (h : S.CanConcat p) (hp : p.initial.reducedToSet S) :
    S.IsWeakAscendingSet → (S.concat p).IsWeakAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_add_one (S.length_concat h ▸ hj)
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rw [if_pos hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp _ <| apply_mem hi

theorem isWeakAscendingSet_takeConcat (hp : p.initial.reducedToSet S) :
    S.IsWeakAscendingSet → (S.takeConcat p).IsWeakAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isWeakAscendingSet_single p
  refine TriangularSet.isWeakAscendingSet_concat _ (fun n hn ↦ ?_) <| isWeakAscendingSet_take _ h
  apply hp
  exact TriangularSet.take_subset S _ <| mem_def.mpr hn

end TriangularSet

namespace MvPolynomial

namespace List

variable {isAscendingSet : TriangularSet σ R → Prop} [AscendingSetTheory σ R isAscendingSet]
variable (l : List (MvPolynomial σ R)) {l1 l2 : List (MvPolynomial σ R)} {S T : TriangularSet σ R}

/-- The Basic Set of a list `l`, as computed by the `AscendingSetTheory` instance. -/
def basicSet (isAscendingSet : TriangularSet σ R → Prop) [AscendingSetTheory σ R isAscendingSet]
    (l : List (MvPolynomial σ R)) : TriangularSet σ R :=
  AscendingSetTheory.basicSet isAscendingSet l

theorem basicSet_subset : ↑(l.basicSet isAscendingSet) ⊆ {p | p ∈ l} :=
  AscendingSetTheory.basicSet_subset l

theorem basicSet_minimal : ∀ ⦃S⦄, isAscendingSet S → ↑S ⊆ {p | p ∈ l} →
    (l.basicSet isAscendingSet) ≤ S :=
  fun _ hS ↦ AscendingSetTheory.basicSet_minimal l hS

theorem basicSet_isAscendingSet : isAscendingSet (l.basicSet isAscendingSet) :=
  AscendingSetTheory.basicSet_isAscendingSet l

theorem basicSet_toList_equiv :
    (l.basicSet isAscendingSet).toList.basicSet isAscendingSet ≈ l.basicSet isAscendingSet := by
  refine And.intro ?_ ?_
  <;> apply basicSet_minimal
  · exact basicSet_isAscendingSet _
  · intro p hp
    exact TriangularSet.mem_toList_iff.mpr hp
  · exact basicSet_isAscendingSet _
  intro p hp
  exact l.basicSet_subset <| TriangularSet.mem_toList_iff.mp <| basicSet_subset _ hp

theorem basicSet_ge_of_subset : l1 ⊆ l2 → l2.basicSet isAscendingSet ≤ l1.basicSet isAscendingSet :=
  fun h ↦ l2.basicSet_minimal l1.basicSet_isAscendingSet fun _ hp ↦ h <| l1.basicSet_subset hp

theorem basicSet_append_comm :
    (l1 ++ l2).basicSet isAscendingSet ≈ (l2 ++ l1).basicSet isAscendingSet :=
  have (l1 l2 : List (MvPolynomial σ R)) : l2 ++ l1 ⊆ l1 ++ l2 := List.append_subset.mpr ⟨
    List.subset_append_of_subset_right l1 fun _ ↦ id,
    List.subset_append_of_subset_left l2 fun _ ↦ id⟩
  And.intro (basicSet_ge_of_subset <| this l1 l2) (basicSet_ge_of_subset <| this l2 l1)

theorem basicSet_append_lt_of_exists_reducedToSet
    (h : ∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (l1.basicSet isAscendingSet)) :
      (l2 ++ l1).basicSet isAscendingSet < l1.basicSet isAscendingSet :=
  AscendingSetTheory.basicSet_append_lt_of_exists_reducedToSet h

theorem _root_.TriangularSet.basicSet_toList_le_of_isAscendingSet {S : TriangularSet σ R}
    (hS : isAscendingSet S) : S.toList.basicSet isAscendingSet ≤ S := by
  apply S.toList.basicSet_minimal hS
  simp only [TriangularSet.mem_toList_iff, SetLike.setOf_mem_eq, subset_refl]

end MvPolynomial.List

open TriangularSet

namespace IsAscendingSet

variable (l : List (MvPolynomial σ R))

/-- The recursive algorithm for computing the Standard Basic Set. -/
noncomputable def basicSet.go (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : TriangularSet σ R :=
  match l with
  | [] => BS
  | B :: tail =>
    let BS' := BS.takeConcat B
    let l' := (B :: tail).filter (reducedToSet · BS')
    go l' BS' (fun p hp ↦ hl1 p <| List.mem_of_mem_filter hp)
  termination_by l.length
  decreasing_by
    refine List.length_filter_lt_length_iff_exists.mpr ⟨B, by simp, ?_⟩
    refine ne_true_of_eq_false <| decide_eq_false ?_
    simp only [reducedToSet, not_forall]
    have : B ≠ 0 := by by_contra! rfl; simp at hl1
    exact ⟨B, mem_takeConcat BS this, not_reduceTo_self this⟩

/--
Computes the Standard Basic Set of a list of polynomials.
The algorithm works by:
1. Sort the list and let `BS = ∅`.
2. Pick the first (minimal) element `B` in the list.
3. Update the current basic set `BS` with `B` using `takeConcat` (which handles replacements).
4. Filter the remaining list to keep only elements reduced w.r.t. the new `BS` and go to step 2.
-/
noncomputable def basicSet : TriangularSet σ R :=
  basicSet.go (l.mergeSort.filter (· ≠ 0)) ∅ (fun _ h ↦ of_decide_eq_true (List.mem_filter.mp h).2)

lemma basicSetGo_lt (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (h : l ≠ []) (hl2 : (l.head h).reducedToSet BS) :
    basicSet.go l BS hl1 < BS := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 => simp at h
  | case2 BS B tail hl1 BS' l' _ ih =>
    rw [basicSet.go]
    change basicSet.go l' BS' _ < BS
    have : BS' < BS := takeConcat_lt_of_reducedToSet (hl1 _ <| List.head_mem h) hl2
    by_cases h' : l' = []
    · rw! [h', basicSet.go]
      exact this
    · exact lt_trans (ih h' <| of_decide_eq_true (List.mem_filter.mp <| List.head_mem h').2) this

lemma basicSetGo_le (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (hl2 : l.head?.all (fun p ↦ p.reducedToSet BS)) :
    basicSet.go l BS hl1 ≤ BS := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 => simp [basicSet.go]
  | case2 BS B tail hl1 _ _ _ =>
    rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hl2
    exact le_of_lt <| basicSetGo_lt (B :: tail) BS hl1 (by simp) hl2

lemma mem_of_mem_basicSetGo (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : ∀ p, p ∉ BS → p ∈ basicSet.go l BS hl1 → p ∈ l := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 => simp only [basicSet.go, List.not_mem_nil, imp_false, imp_self, implies_true]
  | case2 BS B tail hl1 BS' l' h ih =>
      intro p hp1 hp2
      rw [basicSet.go] at hp2
      change p ∈ basicSet.go l' BS' _ at hp2
      have hnotMem : p = B ∨ p ∉ BS' :=
        or_not_of_imp fun h ↦ not_not.mp <| ne_eq _ _ ▸ (mt <| takeConcat_subset p h) hp1
      match hnotMem with
      | .inl hm => exact List.mem_cons.mpr <| Or.inl hm
      | .inr hm => exact List.mem_of_mem_filter <| ih p hm hp2

lemma basicSetGo_isAscendingSet (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : l.head?.all (fun p ↦ p.reducedToSet BS) → BS.IsAscendingSet →
    (basicSet.go l BS hl1).IsAscendingSet := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 => unfold basicSet.go; simp
  | case2 BS B tail hl1 BS' l' h ih =>
      intro hBS1 hBS2
      rw [basicSet.go]
      rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hBS1
      refine ih ?_ <| isAscendingSet_takeConcat hBS1 hBS2
      if l'_nil : l' = [] then simp [l'_nil]
      else
        simp only [List.head?_eq_some_head l'_nil, Option.all_some, decide_eq_true_eq]
        exact of_decide_eq_true (List.mem_filter.mp <| List.head_mem l'_nil).2

/-- The core lemma proving that the computed Basic Set is indeed minimal
among all ascending sets contained in `l`. -/
lemma basicSetGo_le_ascendingSet (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : l.Pairwise (· ≤ ·) → (∀ p ∈ l, BS.CanConcat p) →
    l.head?.all (reducedToSet · BS) →
    ∀ T, T.IsAscendingSet → (BS.length ≤ T.length ∧ ∀ i < BS.length, BS i ≈ T i) →
    (∀ p ∈ T, (∀ i < BS.length, ¬ BS i ≈ p) → p ∈ l) → basicSet.go l BS hl1 ≤ T := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 BS hl1 =>
    intro _ _ _ T _ _ hT4
    rw [basicSet.go]
    refine ge_of_forall_equiv fun n hn ↦ ?_
    simpa using hT4 _ (apply_mem hn)
  | case2 BS B tail hl1 BS' l' _ ih =>
    intro hl2 hBS1 hBS2 T hT1 ⟨hT2, hT3⟩ hT4
    have hB1 := hBS1 B List.mem_cons_self
    have hB2 : ∀ ⦃q⦄, q ∈ B :: tail → B ≤ q := fun _ ↦ List.Pairwise.rel_head hl2
    rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hBS2
    have heq : BS' = BS.concat B := takeConcat_eq_concat_of_canConcat hB1
    by_cases hL : T.length = BS.length
    · have : BS ≈ T := equiv_iff'.mpr ⟨hL.symm, hT3⟩
      refine le_of_lt <| TriangularSet.lt_of_lt_of_equiv ?_ this
      exact basicSetGo_lt (B :: tail) BS hl1 (by simp) hBS2
    have hL : BS.length < T.length := Nat.lt_of_le_of_ne hT2 (Ne.symm hL)
    rw [basicSet.go]
    change basicSet.go l' BS' _ ≤ T
    let q := T BS.length
    have Bleq : B ≤ q := by
      refine hB2 <| (hT4 q <| apply_mem hL) fun i hi ↦ ?_
      apply not_antisymmRel_of_lt
      rw [AntisymmRel.lt_congr_left <| hT3 i hi]
      exact apply_lt_of_index_lt hL hi
    have hBS2' : l'.head?.all (reducedToSet · BS') := by
      simp only [Option.all_eq_true, decide_eq_true_eq]
      intro r hr
      have : r ∈ l' := List.mem_of_mem_head? hr
      exact of_decide_eq_true (List.mem_filter.mp this).2
    -- Main Logic: Compare B (from algo) and q (from T)
    rcases  le_iff_lt_or_equiv.mp Bleq with Bltq | hBq
    · -- Case 1: B < q. The algorithm picked a smaller element, so BS' < T.
      have : BS' < T := by
        rw [heq]
        apply TriangularSet.lt_def.mpr
        refine Or.inl ⟨BS.length, BS.length_concat _ ▸ lt_add_one _, ?_, fun i hi ↦ ?_⟩
        · simpa [concat_apply] using Bltq
        rw [concat_apply, if_pos hi]
        exact hT3 i hi
      refine le_trans ?_ (le_of_lt this)
      exact basicSetGo_le _ _ _ hBS2'
    -- Case 2: B ≈ q. They match, so we proceed recursively.
    have hBS1' : ∀ p ∈ l', BS'.CanConcat p := fun p hp ↦ by
      simp only [l', heq, List.mem_filter, decide_eq_true_eq, reducedToSet_iff] at hp ⊢
      refine ⟨hl1 p hp.1, fun _ ↦ ?_⟩
      have := hp.2 BS.length (BS.length_concat _ ▸ lt_add_one _)
      simp only [concat_apply, lt_self_iff_false, ↓reduceIte, length_concat,
        add_tsub_cancel_right, gt_iff_lt] at this ⊢
      exact max_vars_lt_of_reducedTo_of_le (hl1 p hp.1) (hB2 hp.1) this
    refine ih (List.Pairwise.filter _ hl2) hBS1' hBS2' T hT1 ⟨?_, fun i hi ↦ ?_⟩ ?_
    · rw [heq, BS.length_concat]
      exact hL
    · simp only [heq, length_concat, concat_apply] at hi ⊢
      split_ifs with hi1 hi2
      · exact hT3 i hi1
      · exact hi2 ▸ hBq
      absurd hi1
      exact lt_of_le_of_ne (Nat.le_of_lt_succ hi) hi2
    intro p hp1 hp2
    simp only [l', List.mem_filter, decide_eq_true_eq, heq] at hp2 ⊢
    have hp2 : ¬ B ≈ p ∧ ∀ i < BS.length, ¬ BS i ≈ p := by
      simp only [length_concat, concat_apply] at hp2
      constructor
      · simpa using hp2 BS.length (lt_add_one _)
      intro i hi
      simpa [hi] using hp2 i (Nat.lt_add_right 1 hi)
    refine ⟨hT4 p hp1 hp2.2, reducedToSet_iff.mpr fun i hi ↦ ?_⟩
    rcases hp1 with ⟨k, hk1, hk2⟩
    have hk3 : BS.length < k := by
      contrapose! hp2
      refine fun hp3 ↦ ⟨k, ?_⟩
      have : k ≠ BS.length := fun this ↦ absurd hp3 (by rw [not_not, ← hk2, this]; exact hBq)
      have : k < BS.length := lt_of_le_of_ne hp2 this
      exact ⟨this, hk2 ▸ hT3 k this⟩
    rw [← hk2, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right <| hT3 i hi1).mpr <| hT1 (lt_trans hi1 hk3) hk1
    · exact (reducedTo_congr_right hBq).mpr <| hT1 hk3 hk1
    absurd hi1
    exact lt_of_le_of_ne (Nat.le_of_lt_add_one (BS.length_concat _ ▸ hi)) hi2

protected lemma basicSet_isAscendingSet : (basicSet l).IsAscendingSet :=
  basicSetGo_isAscendingSet _ _ _ Option.all_true isAscendingSet_empty

protected lemma basicSet_subset : ∀ ⦃p : MvPolynomial σ R⦄, p ∈ basicSet l → p ∈ l := fun p hp ↦
  List.mem_mergeSort.mp <|
    List.mem_of_mem_filter (mem_of_mem_basicSetGo _ ∅ _ p (notMem_empty p) hp)

protected lemma basicSet_minimal : ∀ ⦃S : TriangularSet σ R⦄, S.IsAscendingSet →
    (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S := fun S hS1 hS2 ↦ by
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  have hsl2 : sl.Pairwise (· ≤ ·) := List.Pairwise.filter _ <| l.pairwise_mergeSort' (· ≤ ·)
  refine basicSetGo_le_ascendingSet _ ∅ hsl1 hsl2 (fun q hq ↦ empty_canConcat (hsl1 q hq))
      Option.all_true S hS1 (by simp) (fun p hp1 _ ↦ List.mem_filter.mpr ?_)
  exact ⟨List.mem_mergeSort.mpr (hS2 hp1), decide_eq_true <| ne_zero_of_mem hp1⟩

/-- The Standard Basic Set algorithm satisfies the abstract `AscendingSetTheory` interface. -/
noncomputable instance : AscendingSetTheory σ R IsAscendingSet where
  initial_reducedToSet_of_max_vars_ne_bot := fun p i h hc hp ⟨j, hj1, hj2⟩ ↦ by
    match em (i = j) with
    | .inl hij =>
      rw [← hj2, ← hij]
      exact initial_reducedTo_self hc
    | .inr hij =>
      apply initial_reducedTo
      rw [← hj2]
      match lt_or_gt_of_ne hij with
      | .inl hij => exact reducedTo_of_max_vars_lt <| max_vars_lt_of_index_lt hj1 hij
      | .inr hij => exact (isAscendingSet_iff.mp h) hij hj1
  basicSet := basicSet
  basicSet_isAscendingSet := IsAscendingSet.basicSet_isAscendingSet
  basicSet_subset := IsAscendingSet.basicSet_subset
  basicSet_minimal := IsAscendingSet.basicSet_minimal
  basicSet_append_lt_of_exists_reducedToSet l1 l2 := fun ⟨p, hp1, hp2, hp3⟩ ↦ by
    let S := (basicSet l1).takeConcat p
    have hS1 : S.IsAscendingSet := isAscendingSet_takeConcat
      hp3 (IsAscendingSet.basicSet_isAscendingSet l1)
    have hS2 : S < basicSet l1 := takeConcat_lt_of_reducedToSet hp2 hp3
    refine lt_of_le_of_lt (IsAscendingSet.basicSet_minimal _ hS1 fun q hq ↦ ?_) hS2
    refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
    apply IsAscendingSet.basicSet_subset l1
    exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

end IsAscendingSet

namespace IsWeakAscendingSet

variable (l : List (MvPolynomial σ R))

/-- The recursive algorithm for computing the Weak Basic Set. -/
noncomputable def basicSet.go (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (hl2 : ∀ p ∈ l, BS.CanConcat p) : TriangularSet σ R :=
  match l with
  | [] => BS
  | B :: tail =>
    have hB : BS.CanConcat B := hl2 B List.mem_cons_self
    let BS' := BS.concat B
    -- Explicitly check main variable ordering here:
    let l' := (B :: tail).filter fun p ↦ B.vars.max < p.vars.max ∧ p.initial.reducedToSet BS'
    have hl1' : ∀ p ∈ l', p ≠ 0 := fun p hp ↦ hl1 p (List.mem_of_mem_filter hp)
    have hl2' : ∀ p ∈ l', BS'.CanConcat p := fun p hp ↦
      have := List.mem_filter.mp hp
      ⟨hl1 p this.1, fun _ ↦ by
        rw [concat_apply, length_concat]
        simp only [add_tsub_cancel_right, lt_self_iff_false, ↓reduceIte]
        exact (of_decide_eq_true this.2).1⟩
    go l' BS' hl1' hl2'
  termination_by l.length
  decreasing_by
    refine List.length_filter_lt_length_iff_exists.mpr ⟨B, List.mem_cons_self, ?_⟩
    refine ne_true_of_eq_false <| decide_eq_false ?_
    rw [not_and_or, not_lt]
    exact Or.inl (le_refl _)

/--
Computes the Weak Basic Set of a list of polynomials.
Difference from Standard:
The filter condition includes `B.max_vars < p.max_vars`.
This is because `p.initial.reducedTo B` does NOT imply `B.max_vars < p.max_vars`
(unlike strong reduction).
We must enforce the triangular structure explicitly.
-/
noncomputable def basicSet : TriangularSet σ R :=
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  basicSet.go sl ∅ hsl1 (fun p hp ↦ empty_canConcat <| hsl1 p hp)

lemma basicSetGo_lt (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.CanConcat p) : (h : l ≠ []) →
    (l.head h).initial.reducedToSet BS → basicSet.go l BS hl1 hl2 < BS := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 _ _ _ => simp
  | case2 BS B tail _ _ hB BS' l' hl1' hl2' _ _ ih =>
    intro _ _
    rw [basicSet.go]
    change basicSet.go l' BS' hl1' hl2' < BS
    have : BS' < BS := concat_lt hB
    if h' : l' = [] then
      simp only [h', basicSet.go, gt_iff_lt]
      exact concat_lt hB
    else
      have := ih h' (of_decide_eq_true (List.mem_filter.mp <| List.head_mem h').2).2
      exact lt_trans this (concat_lt hB)

lemma basicSetGo_le (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.CanConcat p) :
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) → basicSet.go l BS hl1 hl2 ≤ BS := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 _ _ _ => unfold basicSet.go; simp
  | case2 BS B tail hl1 hl2 _ _ _ _ _ _ _ _ =>
    intro hl3
    rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hl3
    exact le_of_lt <| basicSetGo_lt (B :: tail) BS hl1 hl2 (by simp) hl3

lemma mem_of_mem_basicSetGo (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.CanConcat p) :
    ∀ p, p ∉ BS → p ∈ basicSet.go l BS hl1 hl2 → p ∈ l := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 _ _ _ => unfold basicSet.go; simp
  | case2 BS B tail _ _ hB BS' l' hl1' hl2' _ _ ih =>
    intro p hp1 hp2
    rw [basicSet.go] at hp2
    change p ∈ basicSet.go l' BS' hl1' hl2' at hp2
    have hnotMem : p = B ∨ p ∉ BS' :=
      or_not_of_imp fun h ↦ or_iff_not_imp_right.mp ((mem_concat_iff hB).mp h) hp1
    match hnotMem with
    | .inl hm => exact List.mem_cons.mpr <| Or.inl hm
    | .inr hm => exact List.mem_of_mem_filter <| ih p hm hp2

lemma basicSetGo_isAscendingSet (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (hl2 : ∀ p ∈ l, BS.CanConcat p) :
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) → BS.IsWeakAscendingSet →
    (basicSet.go l BS hl1 hl2).IsWeakAscendingSet := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 _ _ _ => unfold basicSet.go; simp
  | case2 BS B tail _ _ hB BS' l' hl1' hl2' _ _ ih =>
    expose_names
    intro hl3 hBS
    rw [basicSet.go]
    rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hl3
    refine ih ?_ <| isWeakAscendingSet_concat hB hl3 hBS
    if l'_nil : l' = [] then simp [l'_nil]
    else
      simp only [List.head?_eq_some_head l'_nil, Option.all_some, decide_eq_true_eq]
      exact (of_decide_eq_true (List.mem_filter.mp <| List.head_mem l'_nil).2).2

lemma basicSetGo_le_ascendingSet (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.CanConcat p) : l.Pairwise (· ≤ ·) →
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) →
    ∀ T, T.IsWeakAscendingSet → (BS.length ≤ T.length ∧ ∀ i < BS.length, BS i ≈ T i) →
    (∀ p ∈ T, (∀ i < BS.length, ¬ BS i ≈ p) → p ∈ l) → basicSet.go l BS hl1 hl2 ≤ T := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 =>
    intro _ _ T _ _ hT4
    rw [basicSet.go]
    refine ge_of_forall_equiv fun n hn ↦ ?_
    simpa using hT4 _ (apply_mem hn)
  | case2 BS B tail hl1 hl2 hB BS' l' hl1' hl2' _ _ ih =>
    intro hl3 hBS T hT1 ⟨hT2, hT3⟩ hT4
    have hB1 := hl1 B List.mem_cons_self
    have hB2 : ∀ ⦃q⦄, q ∈ B :: tail → B ≤ q := fun _ ↦ List.Pairwise.rel_head hl3
    rw [List.head?_cons, Option.all_some, decide_eq_true_eq] at hBS
    by_cases hL : T.length = BS.length
    · have : BS ≈ T := equiv_iff'.mpr ⟨hL.symm, hT3⟩
      refine le_of_lt <| TriangularSet.lt_of_lt_of_equiv ?_ this
      exact basicSetGo_lt (B :: tail) BS hl1 hl2 (by simp) hBS
    have hL : BS.length < T.length := Nat.lt_of_le_of_ne hT2 (Ne.symm hL)
    rw [basicSet.go]
    change basicSet.go l' BS' hl1' hl2' ≤ T
    let q := T BS.length
    have Bleq : B ≤ q := by
      refine hB2 <| (hT4 q <| apply_mem hL) fun i hi ↦ ?_
      apply not_antisymmRel_of_lt
      rw [AntisymmRel.lt_congr_left <| hT3 i hi]
      exact apply_lt_of_index_lt hL hi
    have hBS' : l'.head?.all (fun p ↦ p.initial.reducedToSet BS') := by
      simp only [Option.all_eq_true, decide_eq_true_eq]
      intro r hr
      have : r ∈ l' := List.mem_of_mem_head? hr
      exact And.right <| of_decide_eq_true (List.mem_filter.mp this).2
    rcases  le_iff_lt_or_equiv.mp Bleq with Bltq | hBq
    · have : BS' < T := by
        apply TriangularSet.lt_def.mpr
        refine Or.inl ⟨BS.length, BS.length_concat _ ▸ lt_add_one _, ?_, fun i hi ↦ ?_⟩
        · simpa [BS', concat_apply] using Bltq
        rw [concat_apply, if_pos hi]
        exact hT3 i hi
      refine le_trans ?_ (le_of_lt this)
      exact basicSetGo_le l' BS' hl1' hl2' hBS'
    refine ih (List.Pairwise.filter _ hl3) hBS' T hT1 ⟨BS.length_concat _ ▸ hL, fun i hi ↦ ?_⟩ ?_
    · simp only [BS', length_concat, concat_apply] at hi ⊢
      split_ifs with hi1 hi2
      · exact hT3 i hi1
      · exact hi2 ▸ hBq
      absurd hi1
      exact lt_of_le_of_ne (Nat.le_of_lt_succ hi) hi2
    intro p hp1 hp2
    simp only [l', List.mem_filter, decide_eq_true_eq, BS'] at hp2 ⊢
    have hp2 : ¬ B ≈ p ∧ ∀ i < BS.length, ¬ BS i ≈ p := by
      simp only [length_concat, concat_apply] at hp2
      constructor
      · simpa using hp2 BS.length (lt_add_one _)
      intro i hi
      simpa [hi] using hp2 i (Nat.lt_add_right 1 hi)
    refine ⟨hT4 p hp1 hp2.2, ?_, reducedToSet_iff.mpr fun i hi ↦ ?_⟩
    <;> rcases hp1 with ⟨k, hk1, hk2⟩
    · simp only [(equiv_iff.mp hBq).1, ← hk2] at hp2 ⊢
      refine max_vars_lt_of_index_lt hk1 ?_
      contrapose! hp2
      intro hk3
      rcases lt_or_eq_of_le hp2 with hk2 | hk2
      · exact ⟨k, hk2, hT3 k hk2⟩
      exact absurd hk3 <| not_not.mpr <| hk2 ▸ hBq
    have hk3 : BS.length < k := by
      contrapose! hp2
      refine fun hp3 ↦ ⟨k, ?_⟩
      have : k ≠ BS.length := fun this ↦ absurd hp3 (by rw [not_not, ← hk2, this]; exact hBq)
      have : k < BS.length := lt_of_le_of_ne hp2 this
      exact ⟨this, hk2 ▸ hT3 k this⟩
    rw [← hk2, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right <| hT3 i hi1).mpr <| hT1 (lt_trans hi1 hk3) hk1
    · exact (reducedTo_congr_right hBq).mpr <| hT1 hk3 hk1
    absurd hi1
    exact lt_of_le_of_ne (Nat.le_of_lt_add_one (BS.length_concat _ ▸ hi)) hi2

protected lemma basicSet_isWeakAscendingSet : (basicSet l).IsWeakAscendingSet :=
  basicSetGo_isAscendingSet _ _ _ _ Option.all_true isAscendingSet_empty

protected lemma basicSet_subset : ∀ ⦃p : MvPolynomial σ R⦄, p ∈ basicSet l → p ∈ l := fun p hp ↦
  List.mem_mergeSort.mp <|
    List.mem_of_mem_filter (mem_of_mem_basicSetGo _ ∅ _ _ p (notMem_empty p) hp)

protected lemma basicSet_minimal : ∀ ⦃S : TriangularSet σ R⦄, S.IsWeakAscendingSet →
    (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S := fun S hS1 hS2 ↦ by
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  have hsl3 : sl.Pairwise (· ≤ ·) := List.Pairwise.filter _ <| l.pairwise_mergeSort' (· ≤ ·)
  refine basicSetGo_le_ascendingSet _ ∅ hsl1 (fun q hq ↦ empty_canConcat (hsl1 q hq)) hsl3
      Option.all_true S hS1 (by simp) (fun p hp1 _ ↦ List.mem_filter.mpr ?_)
  exact ⟨List.mem_mergeSort.mpr (hS2 hp1), decide_eq_true <| ne_zero_of_mem hp1⟩

/-- The Weak Basic Set algorithm satisfies the abstract `AscendingSetTheory` interface. -/
noncomputable instance : AscendingSetTheory σ R IsWeakAscendingSet where
  initial_reducedToSet_of_max_vars_ne_bot := fun p i h hc hp ⟨j, hj1, hj2⟩ ↦ by
    match em (i = j) with
    | .inl hij =>
      rw [← hj2, ← hij]
      exact initial_reducedTo_self hc
    | .inr hij =>
      rw [← hj2]
      match lt_or_gt_of_ne hij with
      | .inl hij =>
        apply initial_reducedTo
        exact reducedTo_of_max_vars_lt <| max_vars_lt_of_index_lt hj1 hij
      | .inr hij => exact (isWeakAscendingSet_iff.mp h) hij hj1
  basicSet := basicSet
  basicSet_isAscendingSet := IsWeakAscendingSet.basicSet_isWeakAscendingSet
  basicSet_subset := IsWeakAscendingSet.basicSet_subset
  basicSet_minimal := IsWeakAscendingSet.basicSet_minimal
  basicSet_append_lt_of_exists_reducedToSet l1 l2 := fun ⟨p, hp1, hp2, hp3⟩ ↦ by
    let S := (basicSet l1).takeConcat p
    have hS1 : S.IsWeakAscendingSet := isWeakAscendingSet_takeConcat
      (initial_reducedToSet hp3) (IsWeakAscendingSet.basicSet_isWeakAscendingSet l1)
    have hS2 : S < basicSet l1 := takeConcat_lt_of_reducedToSet hp2 hp3
    refine lt_of_le_of_lt (IsWeakAscendingSet.basicSet_minimal _ hS1 fun q hq ↦ ?_) hS2
    refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
    apply IsWeakAscendingSet.basicSet_subset l1
    exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

end IsWeakAscendingSet
