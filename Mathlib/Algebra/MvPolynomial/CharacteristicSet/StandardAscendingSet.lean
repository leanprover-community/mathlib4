/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.AscendingSet

/-!
# Standard Ascending Set (Ritt's Definition)

This file implements the theory and algorithm for **Standard Ascending Set**.
In this context, a "Standard Ascending Set" requires that
every element is **reduced** with respect to preceding elements.

## Main declarations

* `AscendingSetTheory`: Implements the theory using `reducedTo` (strong reduction).
* `HasBasicSet`: Provides the `basicSet` algorithm that computes a minimal standard ascending set
  from a list of polynomials.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]

-/

@[expose] public section

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ]

namespace StandardAscendingSet

open MvPolynomial TriangularSet

section AscendingSet

variable {S T : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isAscendingSet_def : isAscendingSet S ↔
    ∀ ⦃i j⦄, i < j → j < S.length → (S j).reducedTo (S i) := Iff.rfl

theorem isAscendingSet_def' : isAscendingSet S ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rewrite [elements_eq_zero_iff.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

theorem reducedTo_of_ne {i j : ℕ} (h : isAscendingSet S) :
    i ≠ j → j < S.length → (S i).reducedTo (S j) := fun hij hj ↦
  match lt_or_gt_of_ne hij with
  | .inl hij => reducedTo_of_mainVariable_lt <| mainVariable_lt_of_index_lt hj hij
  | .inr hij => (isAscendingSet_def'.mp h) hij hj

/-- The standard ascending set theory uses strong reduction `reducedTo`. -/
noncomputable scoped instance : AscendingSetTheory σ R where
  reducedTo' := reducedTo
  initial_reducedToSet_of_mainVariable_ne_bot := fun _ i h hc _ ⟨j, hj1, hj2⟩ ↦
    match em (i = j) with
    | .inl hij => hj2 ▸ hij ▸ initial_reducedTo_self hc
    | .inr hij => initial_reducedTo <| hj2 ▸ reducedTo_of_ne h hij hj1

theorem isAscendingSet_concat (h : S.canConcat p) (hp : p.reducedToSet S) :
    S.isAscendingSet → (S.concat p).isAscendingSet :=
  TriangularSet.isAscendingSet_concat h (reducedToSet_iff.mp hp)

theorem isAscendingSet_takeConcat (hp : p.reducedToSet S) :
    S.isAscendingSet → (S.takeConcat p).isAscendingSet :=
  TriangularSet.isAscendingSet_takeConcat (reducedToSet_iff.mp hp)

end AscendingSet

variable (l : List (MvPolynomial σ R))

/-- The recursive algorithm for computing the Standard Basic Set. -/
noncomputable def basicSet.go (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : TriangularSet σ R :=
  if h : l = [] then BS
  else
    let B : MvPolynomial σ R := l.head h
    let BS' := BS.takeConcat B
    let l' := l.filter (reducedToSet · BS')
    go l' BS' (fun p hp ↦ hl1 p <| List.mem_of_mem_filter hp)
  termination_by l.length
  decreasing_by
    have : B ∈ l := List.head_mem h
    refine List.length_filter_lt_length_iff_exists.mpr ⟨B, this, ?_⟩
    refine ne_true_of_eq_false <| decide_eq_false ?_
    change ¬B.reducedToSet (BS.takeConcat B)
    simp only [reducedToSet, not_forall]
    have : B ≠ 0 := hl1 B this
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

lemma basicSetGo_lt : ∀ (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (h : l ≠ []), (l.head h).reducedToSet BS → basicSet.go l BS hl1 < BS :=
  basicSet.go.induct _ (by simp)
    (fun l BS hl1 h ih _ hl2 ↦ by
      let B : MvPolynomial σ R := l.head h
      let BS' := BS.takeConcat B
      let l' := l.filter (reducedToSet · BS')
      rewrite [basicSet.go, dif_neg h]
      change basicSet.go l' BS' _ < BS
      have : BS' < BS := takeConcat_lt_of_reducedToSet (hl1 _ <| List.head_mem h) hl2
      if h' : l' = [] then
        rewrite [basicSet.go, dif_pos h']
        exact this
      else
        exact lt_trans (ih h' <| of_decide_eq_true (List.mem_filter.mp <| List.head_mem h').2) this)

lemma basicSetGo_le : ∀ (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0), l.head?.all (fun p ↦ p.reducedToSet BS) → basicSet.go l BS hl1 ≤ BS :=
  basicSet.go.induct _ (by unfold basicSet.go; simp)
    (fun l BS hl1 h ih hl2 ↦ by
      rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hl2
      exact le_of_lt <| basicSetGo_lt l BS hl1 h hl2)

lemma mem_of_mem_basicSetGo : ∀ (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0), ∀ p, p ∉ BS → p ∈ basicSet.go l BS hl1 → p ∈ l :=
  basicSet.go.induct _ (by simp [basicSet.go])
    (fun l BS hl1 h ih p hp1 hp2 ↦ by
      let B : MvPolynomial σ R := l.head h
      let BS' := BS.takeConcat B
      let l' := l.filter (reducedToSet · BS')
      rewrite [basicSet.go, dif_neg h] at hp2
      change p ∈ basicSet.go l' BS' _ at hp2
      have hnotMem : p = B ∨ p ∉ BS' :=
        or_not_of_imp fun h ↦ not_not.mp <| ne_eq _ _ ▸ (mt <| takeConcat_subset p h) hp1
      match hnotMem with
      | .inl hm => exact hm ▸ List.head_mem h
      | .inr hm => exact List.mem_of_mem_filter <| ih p hm hp2)

lemma basicSetGo_isAscendingSet : ∀ (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0), l.head?.all (fun p ↦ p.reducedToSet BS) → BS.isAscendingSet →
    (basicSet.go l BS hl1).isAscendingSet :=
  basicSet.go.induct _ (fun BS _ _ ↦ by unfold basicSet.go; simp)
    (fun l BS hl1 h ih hBS1 hBS2 ↦ by
      let B : MvPolynomial σ R := l.head h
      let BS' := BS.takeConcat B
      let l' := l.filter (reducedToSet · BS')
      rewrite [basicSet.go, dif_neg h]
      rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hBS1
      refine ih (?_ : l'.head?.all (reducedToSet · BS')) <|
        isAscendingSet_takeConcat hBS1 hBS2
      if l'_nil : l' = [] then simp [l'_nil]
      else
        simp only [List.head?_eq_some_head l'_nil, Option.all_some, decide_eq_true_eq]
        exact of_decide_eq_true (List.mem_filter.mp <| List.head_mem l'_nil).2)

/-- The core lemma proving that the computed Basic Set is indeed minimal
among all ascending sets contained in `l`. -/
lemma basicSetGo_le_ascendingSet (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) : l.Pairwise (· ≤ ·) → (∀ p ∈ l, BS.canConcat p) →
    l.head?.all (reducedToSet · BS) →
    ∀ T, T.isAscendingSet → (BS.length ≤ T.length ∧ ∀ i < BS.length, BS i ≈ T i) →
    (∀ p ∈ T, (∀ i < BS.length, ¬ BS i ≈ p) → p ∈ l) → basicSet.go l BS hl1 ≤ T := by
  induction l, BS, hl1 using basicSet.go.induct with
  | case1 BS hl1 =>
    intro _ _ _ T _ _ hT4
    rewrite [basicSet.go, dif_pos rfl]
    refine ge_of_forall_equiv fun n hn ↦ ?_
    simpa using hT4 _ (apply_mem hn)
  | case2 l BS hl1 h B BS' l' ih =>
    intro hl2 hBS1 hBS2 T hT1 ⟨hT2, hT3⟩ hT4
    have hB1 := hBS1 B <| List.head_mem h
    have hB2 : ∀ ⦃q⦄, q ∈ l → B ≤ q := fun _ ↦ List.Pairwise.rel_head hl2
    rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hBS2
    have heq : BS' = BS.concat B := takeConcat_eq_concat_of_canConcat hB1
    by_cases hL : T.length = BS.length
    · have : BS ≈ T := equiv_iff'.mpr ⟨hL.symm, hT3⟩
      refine le_of_lt <| TriangularSet.lt_of_lt_of_equiv ?_ this
      exact basicSetGo_lt l BS hl1 h hBS2
    have hL : BS.length < T.length := Nat.lt_of_le_of_ne hT2 (Ne.symm hL)
    rewrite [basicSet.go, dif_neg h]
    change basicSet.go l' BS' _ ≤ T
    let q := T BS.length
    have Bleq : B ≤ q := by
      refine hB2 <| (hT4 q <| apply_mem hL) fun i hi ↦ ?_
      apply not_antisymmRel_of_lt
      rewrite [AntisymmRel.lt_congr_left <| hT3 i hi]
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
        rewrite [heq]
        refine TriangularSet.lt_def.mpr <| Or.inl ⟨BS.length, lt_add_one _, ?_, fun i hi ↦ ?_⟩
        · simpa [concat_apply] using Bltq
        rewrite [concat_apply, if_pos hi]
        exact hT3 i hi
      refine le_trans ?_ (le_of_lt this)
      exact basicSetGo_le _ _ _ hBS2'
    -- Case 2: B ≈ q. They match, so we proceed recursively.
    have hBS1' : ∀ p ∈ l', BS'.canConcat p := fun p hp ↦ by
      simp only [l', heq, List.mem_filter, decide_eq_true_eq, reducedToSet_iff] at hp ⊢
      refine ⟨hl1 p hp.1, fun _ ↦ ?_⟩
      have := hp.2 BS.length (lt_add_one _)
      simp only [concat_apply, lt_self_iff_false, ↓reduceIte, length_concat,
        add_tsub_cancel_right, gt_iff_lt] at this ⊢
      exact mainVariable_lt_of_reducedTo_of_le (hl1 p hp.1) (hB2 hp.1) this
    refine ih (List.Pairwise.filter _ hl2) hBS1' hBS2' T hT1 ⟨heq ▸ hL, fun i hi ↦ ?_⟩ ?_
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
    refine ⟨hT4 p hp1 hp2.2, reducedToSet_iff.mpr fun i (hi : i < BS.length + 1) ↦ ?_⟩
    rcases hp1 with ⟨k, hk1, hk2⟩
    have hk3 : BS.length < k := by
      contrapose! hp2
      refine fun hp3 ↦ ⟨k, ?_⟩
      have : k ≠ BS.length := fun this ↦ absurd hp3 (by rw [not_not, ← hk2, this]; exact hBq)
      have : k < BS.length := lt_of_le_of_ne hp2 this
      exact ⟨this, hk2 ▸ hT3 k this⟩
    rewrite [← hk2, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right <| hT3 i hi1).mpr <| hT1 (lt_trans hi1 hk3) hk1
    · exact (reducedTo_congr_right hBq).mpr <| hT1 hk3 hk1
    absurd hi1
    exact lt_of_le_of_ne (Nat.le_of_lt_succ hi) hi2

protected lemma basicSet_isAscendingSet : (basicSet l).isAscendingSet :=
  basicSetGo_isAscendingSet _ _ _ Option.all_true isAscendingSet_empty

protected lemma basicSet_subset : ∀ ⦃p : MvPolynomial σ R⦄, p ∈ basicSet l → p ∈ l := fun p hp ↦
  List.mem_mergeSort.mp <|
    List.mem_of_mem_filter (mem_of_mem_basicSetGo _ ∅ _ p (notMem_empty p) hp)

protected lemma basicSet_minimal : ∀ ⦃S : TriangularSet σ R⦄, S.isAscendingSet →
    (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S := fun S hS1 hS2 ↦ by
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  have hsl2 : sl.Pairwise (· ≤ ·) := List.Pairwise.filter _ <| l.pairwise_mergeSort' (· ≤ ·)
  refine basicSetGo_le_ascendingSet _ ∅ hsl1 hsl2 (fun q hq ↦ empty_canConcat (hsl1 q hq))
      Option.all_true S hS1 (by simp) (fun p hp1 _ ↦ List.mem_filter.mpr ?_)
  exact ⟨List.mem_mergeSort.mpr (hS2 hp1), decide_eq_true <| ne_zero_of_mem hp1⟩

/-- The Standard Basic Set algorithm satisfies the abstract `HasBasicSet` interface. -/
noncomputable scoped instance : HasBasicSet σ R where
  basicSet := basicSet
  basicSet_isAscendingSet := StandardAscendingSet.basicSet_isAscendingSet
  basicSet_subset := StandardAscendingSet.basicSet_subset
  basicSet_minimal := StandardAscendingSet.basicSet_minimal
  basicSet_append_lt_of_exists_reducedToSet l1 l2 := fun ⟨p, hp1, hp2, hp3⟩ ↦ by
    let S := (basicSet l1).takeConcat p
    have hS1 : S.isAscendingSet := isAscendingSet_takeConcat
      hp3 (StandardAscendingSet.basicSet_isAscendingSet l1)
    have hS2 : S < basicSet l1 := takeConcat_lt_of_reducedToSet hp2 hp3
    refine lt_of_le_of_lt (StandardAscendingSet.basicSet_minimal _ hS1 fun q hq ↦ ?_) hS2
    refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
    apply StandardAscendingSet.basicSet_subset l1
    exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

end StandardAscendingSet
