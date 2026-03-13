/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.AscendingSet

/-!
# Weak Ascending Set (Wu's Definition)

This file implements the theory and algorithm for **Weak Ascending Set**,
which are central to Wu's Method.
In this context, a "Weak Ascending Set" requires that the **initial**
of every element is reduced with respect to preceding elements.
This is a weaker condition than the standard reduction.

Consequently, the algorithm for computing a Weak Basic Set must ensure the triangular structure
(strict ascending main variables) explicitly,
by filtering candidates with `B.mainVariable < p.mainVariable`.

## Main declarations

* `AscendingSetTheory`: Implements the theory using `initial.reducedTo` (weak reduction).
* `HasBasicSet`: Provides the `basicSet` algorithm that computes a minimal weak ascending set.
-/

@[expose] public section

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ]

namespace WeakAscendingSet

open MvPolynomial TriangularSet

section AscendingSet

variable {S T : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isAscendingSet_def : isAscendingSet S ↔
    ∀ ⦃i j⦄, i < j → j < S.length → (S j).initial.reducedTo (S i) := Iff.rfl

theorem isAscendingSet_def' : isAscendingSet S ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).initial.reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rewrite [elements_eq_zero_iff.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

theorem initial_reducedTo_of_ne {i j : ℕ} (h : isAscendingSet S) :
    i ≠ j → j < S.length → (S i).initial.reducedTo (S j) := fun hij hj ↦
  match lt_or_gt_of_ne hij with
  | .inl hij =>
    initial_reducedTo <| reducedTo_of_mainVariable_lt <| mainVariable_lt_of_index_lt hj hij
  | .inr hij => (isAscendingSet_def'.mp h) hij hj

/-- The weak ascending set theory uses weak reduction `p.initial.reducedTo`. -/
noncomputable scoped instance : AscendingSetTheory σ R where
  reducedTo' := fun p ↦ p.initial.reducedTo
  initial_reducedToSet_of_mainVariable_ne_bot := fun _ i h hc _ ⟨j, hj1, hj2⟩ ↦
    match em (i = j) with
    | .inl hij => hj2 ▸ hij ▸ initial_reducedTo_self hc
    | .inr hij => hj2 ▸ initial_reducedTo_of_ne h hij hj1

theorem isAscendingSet_concat (h : S.canConcat p) (hp : p.initial.reducedToSet S) :
    S.isAscendingSet → (S.concat p).isAscendingSet :=
  TriangularSet.isAscendingSet_concat h (reducedToSet_iff.mp hp)

theorem isAscendingSet_takeConcat (hp : p.initial.reducedToSet S) :
    S.isAscendingSet → (S.takeConcat p).isAscendingSet :=
  TriangularSet.isAscendingSet_takeConcat (reducedToSet_iff.mp hp)

end AscendingSet

variable (l : List (MvPolynomial σ R))

/-- The recursive algorithm for computing the Weak Basic Set. -/
noncomputable def basicSet.go (l : List (MvPolynomial σ R)) (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (hl2 : ∀ p ∈ l, BS.canConcat p) : TriangularSet σ R :=
  if h : l = [] then BS
  else
    let B : MvPolynomial σ R := l.head h
    have hB : BS.canConcat B := hl2 B (List.head_mem h)
    let BS' := BS.concat B
    -- Explicitly check main variable ordering here:
    let l' := l.filter fun p ↦ B.mainVariable < p.mainVariable ∧ p.initial.reducedToSet BS'
    have hl1' : ∀ p ∈ l', p ≠ 0 := fun p hp ↦ hl1 p (List.mem_of_mem_filter hp)
    have hl2' : ∀ p ∈ l', BS'.canConcat p := fun p hp ↦
      have := List.mem_filter.mp hp
      ⟨hl1 p this.1, fun _ ↦ by
        rewrite [concat_apply, length_concat]
        simp only [add_tsub_cancel_right, lt_self_iff_false, ↓reduceIte]
        exact (of_decide_eq_true this.2).1⟩
    go l' BS' hl1' hl2'
  termination_by l.length
  decreasing_by
    refine List.length_filter_lt_length_iff_exists.mpr ⟨B, List.head_mem h, ?_⟩
    refine ne_true_of_eq_false <| decide_eq_false ?_
    rewrite [not_and_or, not_lt]
    exact Or.inl (le_refl _)

/--
Computes the Weak Basic Set of a list of polynomials.
Difference from Standard:
The filter condition includes `B.mainVariable < p.mainVariable`.
This is because `p.initial.reducedTo B` does NOT imply `B.mainVariable < p.mainVariable`
(unlike strong reduction).
We must enforce the triangular structure explicitly.
-/
noncomputable def basicSet : TriangularSet σ R :=
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  basicSet.go sl ∅ hsl1 (fun p hp ↦ empty_canConcat <| hsl1 p hp)

lemma basicSetGo_lt (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.canConcat p) : (h : l ≠ []) →
    (l.head h).initial.reducedToSet BS → basicSet.go l BS hl1 hl2 < BS := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 => simp
  | case2 l BS hl1 hl2 h B hB BS' l' hl1' hl2' ih =>
    intro _ hl3
    rewrite [basicSet.go, dif_neg h]
    change basicSet.go l' BS' hl1' hl2' < BS
    have : BS' < BS := concat_lt hB
    if h' : l' = [] then
      rewrite [basicSet.go, dif_pos h']
      exact concat_lt hB
    else
      have := ih h' (of_decide_eq_true (List.mem_filter.mp <| List.head_mem h').2).2
      exact lt_trans this (concat_lt hB)

lemma basicSetGo_le (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.canConcat p) :
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) → basicSet.go l BS hl1 hl2 ≤ BS := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 => unfold basicSet.go; simp
  | case2 l BS hl1 hl2 h B hB BS' l' hl1' hl2' ih =>
    intro hl3
    rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hl3
    exact le_of_lt <| basicSetGo_lt l BS hl1 hl2 h hl3

lemma mem_of_mem_basicSetGo (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.canConcat p) :
    ∀ p, p ∉ BS → p ∈ basicSet.go l BS hl1 hl2 → p ∈ l := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 => unfold basicSet.go; simp
  | case2 l BS hl1 hl2 h B hB BS' l' hl1' hl2' ih =>
    intro p hp1 hp2
    rewrite [basicSet.go, dif_neg h] at hp2
    change p ∈ basicSet.go l' BS' hl1' hl2' at hp2
    have hnotMem : p = B ∨ p ∉ BS' :=
      or_not_of_imp fun h ↦ or_iff_not_imp_right.mp ((mem_concat_iff hB).mp h) hp1
    match hnotMem with
    | .inl hm => exact hm ▸ List.head_mem h
    | .inr hm => exact List.mem_of_mem_filter <| ih p hm hp2

lemma basicSetGo_isAscendingSet (BS : TriangularSet σ R)
    (hl1 : ∀ p ∈ l, p ≠ 0) (hl2 : ∀ p ∈ l, BS.canConcat p) :
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) → BS.isAscendingSet →
    (basicSet.go l BS hl1 hl2).isAscendingSet := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 => unfold basicSet.go; simp
  | case2 l BS hl1 hl2 h B hB BS' l' hl1' hl2' =>
    expose_names
    intro hl3 hBS
    rewrite [basicSet.go, dif_neg h]
    rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hl3
    refine ih1 (?_ : l'.head?.all (fun p ↦ p.initial.reducedToSet BS')) <|
      isAscendingSet_concat hB hl3 hBS
    if l'_nil : l' = [] then simp [l'_nil]
    else
      simp only [List.head?_eq_some_head l'_nil, Option.all_some, decide_eq_true_eq]
      exact (of_decide_eq_true (List.mem_filter.mp <| List.head_mem l'_nil).2).2

lemma basicSetGo_le_ascendingSet (BS : TriangularSet σ R) (hl1 : ∀ p ∈ l, p ≠ 0)
    (hl2 : ∀ p ∈ l, BS.canConcat p) : l.Pairwise (· ≤ ·) →
    l.head?.all (fun p ↦ p.initial.reducedToSet BS) →
    ∀ T, T.isAscendingSet → (BS.length ≤ T.length ∧ ∀ i < BS.length, BS i ≈ T i) →
    (∀ p ∈ T, (∀ i < BS.length, ¬ BS i ≈ p) → p ∈ l) → basicSet.go l BS hl1 hl2 ≤ T := by
  induction l, BS, hl1, hl2 using basicSet.go.induct with
  | case1 BS hl1 hl2 =>
    intro _ _ T _ _ hT4
    rewrite [basicSet.go, dif_pos rfl]
    refine ge_of_forall_equiv fun n hn ↦ ?_
    simpa using hT4 _ (apply_mem hn)
  | case2 l BS hl1 hl2 h B hB BS' l' hl1' hl2' ih =>
    intro hl3 hBS T hT1 ⟨hT2, hT3⟩ hT4
    have hB1 := hl1 B <| List.head_mem h
    have hB2 : ∀ ⦃q⦄, q ∈ l → B ≤ q := fun _ ↦ List.Pairwise.rel_head hl3
    rewrite [List.head?_eq_some_head h, Option.all_some, decide_eq_true_eq] at hBS
    by_cases hL : T.length = BS.length
    · have : BS ≈ T := equiv_iff'.mpr ⟨hL.symm, hT3⟩
      refine le_of_lt <| TriangularSet.lt_of_lt_of_equiv ?_ this
      exact basicSetGo_lt l BS hl1 hl2 h hBS
    have hL : BS.length < T.length := Nat.lt_of_le_of_ne hT2 (Ne.symm hL)
    rewrite [basicSet.go, dif_neg h]
    change basicSet.go l' BS' hl1' hl2' ≤ T
    let q := T BS.length
    have Bleq : B ≤ q := by
      refine hB2 <| (hT4 q <| apply_mem hL) fun i hi ↦ ?_
      apply not_antisymmRel_of_lt
      rewrite [AntisymmRel.lt_congr_left <| hT3 i hi]
      exact apply_lt_of_index_lt hL hi
    have hBS' : l'.head?.all (fun p ↦ p.initial.reducedToSet BS') := by
      simp only [Option.all_eq_true, decide_eq_true_eq]
      intro r hr
      have : r ∈ l' := List.mem_of_mem_head? hr
      exact And.right <| of_decide_eq_true (List.mem_filter.mp this).2
    rcases  le_iff_lt_or_equiv.mp Bleq with Bltq | hBq
    · have : BS' < T := by
        refine TriangularSet.lt_def.mpr <| Or.inl ⟨BS.length, lt_add_one _, ?_, fun i hi ↦ ?_⟩
        · simpa [BS', concat_apply] using Bltq
        rewrite [concat_apply, if_pos hi]
        exact hT3 i hi
      refine le_trans ?_ (le_of_lt this)
      exact basicSetGo_le l' BS' hl1' hl2' hBS'
    refine ih (List.Pairwise.filter _ hl3) hBS' T hT1 ⟨hL, fun i hi ↦ ?_⟩ ?_
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
    refine ⟨hT4 p hp1 hp2.2, ?_, reducedToSet_iff.mpr fun i (hi : i < BS.length + 1) ↦ ?_⟩
    <;> rcases hp1 with ⟨k, hk1, hk2⟩
    · simp only [(equiv_iff.mp hBq).1, ← hk2] at hp2 ⊢
      refine mainVariable_lt_of_index_lt hk1 ?_
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
    rewrite [← hk2, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right <| hT3 i hi1).mpr <| hT1 (lt_trans hi1 hk3) hk1
    · exact (reducedTo_congr_right hBq).mpr <| hT1 hk3 hk1
    absurd hi1
    exact lt_of_le_of_ne (Nat.le_of_lt_succ hi) hi2

protected lemma basicSet_isAscendingSet : (basicSet l).isAscendingSet :=
  basicSetGo_isAscendingSet _ _ _ _ Option.all_true isAscendingSet_empty

protected lemma basicSet_subset : ∀ ⦃p : MvPolynomial σ R⦄, p ∈ basicSet l → p ∈ l := fun p hp ↦
  List.mem_mergeSort.mp <|
    List.mem_of_mem_filter (mem_of_mem_basicSetGo _ ∅ _ _ p (notMem_empty p) hp)

protected lemma basicSet_minimal : ∀ ⦃S : TriangularSet σ R⦄, S.isAscendingSet →
    (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S := fun S hS1 hS2 ↦ by
  let sl := l.mergeSort.filter (· ≠ 0)
  have hsl1 : ∀ p ∈ sl, p ≠ 0 := fun _ hp ↦ of_decide_eq_true (List.mem_filter.mp hp).2
  have hsl3 : sl.Pairwise (· ≤ ·) := List.Pairwise.filter _ <| l.pairwise_mergeSort' (· ≤ ·)
  refine basicSetGo_le_ascendingSet _ ∅ hsl1 (fun q hq ↦ empty_canConcat (hsl1 q hq)) hsl3
      Option.all_true S hS1 (by simp) (fun p hp1 _ ↦ List.mem_filter.mpr ?_)
  exact ⟨List.mem_mergeSort.mpr (hS2 hp1), decide_eq_true <| ne_zero_of_mem hp1⟩

/-- The Weak Basic Set algorithm satisfies the abstract `HasBasicSet` interface. -/
noncomputable scoped instance : HasBasicSet σ R where
  basicSet := basicSet
  basicSet_isAscendingSet := WeakAscendingSet.basicSet_isAscendingSet
  basicSet_subset := WeakAscendingSet.basicSet_subset
  basicSet_minimal := WeakAscendingSet.basicSet_minimal
  basicSet_append_lt_of_exists_reducedToSet l1 l2 := fun ⟨p, hp1, hp2, hp3⟩ ↦ by
    let S := (basicSet l1).takeConcat p
    have hS1 : S.isAscendingSet := isAscendingSet_takeConcat
      (initial_reducedToSet hp3) (WeakAscendingSet.basicSet_isAscendingSet l1)
    have hS2 : S < basicSet l1 := takeConcat_lt_of_reducedToSet hp2 hp3
    refine lt_of_le_of_lt (WeakAscendingSet.basicSet_minimal _ hS1 fun q hq ↦ ?_) hS2
    refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
    apply WeakAscendingSet.basicSet_subset l1
    exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

end WeakAscendingSet
