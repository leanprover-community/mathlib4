/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Order.SymmDiff

#align_import measure_theory.decomposition.signed_hahn from "leanprover-community/mathlib"@"bc7d81beddb3d6c66f71449c5bc76c38cb77cf9e"

/-!
# Hahn decomposition

This file proves the Hahn decomposition theorem (signed version). The Hahn decomposition theorem
states that, given a signed measure `s`, there exist complementary, measurable sets `i` and `j`,
such that `i` is positive and `j` is negative with respect to `s`; that is, `s` restricted on `i`
is non-negative and `s` restricted on `j` is non-positive.

The Hahn decomposition theorem leads to many other results in measure theory, most notably,
the Jordan decomposition theorem, the Lebesgue decomposition theorem and the Radon-Nikodym theorem.

## Main results

* `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative` : the Hahn decomposition
  theorem.
* `MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos` : A measurable set of negative
  measure contains a negative subset.

## Notation

We use the notations `0 ≤[i] s` and `s ≤[i] 0` to denote the usual definitions of a set `i`
being positive/negative with respect to the signed measure `s`.

## Tags

Hahn decomposition theorem
-/


noncomputable section

open scoped Classical BigOperators NNReal ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [OrderedAddCommMonoid M]

namespace MeasureTheory

namespace SignedMeasure

open Filter VectorMeasure

variable {s : SignedMeasure α} {i j : Set α}

section ExistsSubsetRestrictNonpos

/-! ### exists_subset_restrict_nonpos

In this section we will prove that a set `i` whose measure is negative contains a negative subset
`j` with respect to the signed measure `s` (i.e. `s ≤[j] 0`), whose measure is negative. This lemma
is used to prove the Hahn decomposition theorem.

To prove this lemma, we will construct a sequence of measurable sets $(A_n)_{n \in \mathbb{N}}$,
such that, for all $n$, $s(A_{n + 1})$ is close to maximal among subsets of
$i \setminus \bigcup_{k \le n} A_k$.

This sequence of sets does not necessarily exist. However, if this sequence terminates; that is,
there does not exists any sets satisfying the property, the last $A_n$ will be a negative subset
of negative measure, hence proving our claim.

In the case that the sequence does not terminate, it is easy to see that
$i \setminus \bigcup_{k = 0}^\infty A_k$ is the required negative set.

To implement this in Lean, we define several auxiliary definitions.

- given the sets `i` and the natural number `n`, `ExistsOneDivLT s i n` is the property that
  there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`.
- given the sets `i` and that `i` is not negative, `findExistsOneDivLT s i` is the
  least natural number `n` such that `ExistsOneDivLT s i n`.
- given the sets `i` and that `i` is not negative, `someExistsOneDivLT` chooses the set
  `k` from `ExistsOneDivLT s i (findExistsOneDivLT s i)`.
- lastly, given the set `i`, `restrictNonposSeq s i` is the sequence of sets defined inductively
  where
  `restrictNonposSeq s i 0 = someExistsOneDivLT s (i \ ∅)` and
  `restrictNonposSeq s i (n + 1) = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq k)`.
  This definition represents the sequence $(A_n)$ in the proof as described above.

With these definitions, we are able consider the case where the sequence terminates separately,
allowing us to prove `exists_subset_restrict_nonpos`.
-/


/-- Given the set `i` and the natural number `n`, `ExistsOneDivLT s i j` is the property that
there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`. -/
private def ExistsOneDivLT (s : SignedMeasure α) (i : Set α) (n : ℕ) : Prop :=
  ∃ k : Set α, k ⊆ i ∧ MeasurableSet k ∧ (1 / (n + 1) : ℝ) < s k

private theorem existsNatOneDivLTMeasure_of_not_negative (hi : ¬s ≤[i] 0) :
    ∃ n : ℕ, ExistsOneDivLT s i n :=
  let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

/-- Given the set `i`, if `i` is not negative, `findExistsOneDivLT s i` is the
least natural number `n` such that `ExistsOneDivLT s i n`, otherwise, it returns 0. -/
private def findExistsOneDivLT (s : SignedMeasure α) (i : Set α) : ℕ :=
  if hi : ¬s ≤[i] 0 then Nat.find (existsNatOneDivLTMeasure_of_not_negative hi) else 0

private theorem findExistsOneDivLT_spec (hi : ¬s ≤[i] 0) :
    ExistsOneDivLT s i (findExistsOneDivLT s i) := by
  rw [findExistsOneDivLT, dif_pos hi]
  -- ⊢ MeasureTheory.SignedMeasure.ExistsOneDivLT s i (Nat.find (_ : ∃ n, MeasureTh …
  convert Nat.find_spec (existsNatOneDivLTMeasure_of_not_negative hi)
  -- 🎉 no goals

private theorem findExistsOneDivLT_min (hi : ¬s ≤[i] 0) {m : ℕ}
    (hm : m < findExistsOneDivLT s i) : ¬ExistsOneDivLT s i m := by
  rw [findExistsOneDivLT, dif_pos hi] at hm
  -- ⊢ ¬MeasureTheory.SignedMeasure.ExistsOneDivLT s i m
  exact Nat.find_min _ hm
  -- 🎉 no goals

/-- Given the set `i`, if `i` is not negative, `someExistsOneDivLT` chooses the set
`k` from `ExistsOneDivLT s i (findExistsOneDivLT s i)`, otherwise, it returns the
empty set. -/
private def someExistsOneDivLT (s : SignedMeasure α) (i : Set α) : Set α :=
  if hi : ¬s ≤[i] 0 then Classical.choose (findExistsOneDivLT_spec hi) else ∅

private theorem someExistsOneDivLT_spec (hi : ¬s ≤[i] 0) :
    someExistsOneDivLT s i ⊆ i ∧
      MeasurableSet (someExistsOneDivLT s i) ∧
        (1 / (findExistsOneDivLT s i + 1) : ℝ) < s (someExistsOneDivLT s i) := by
  rw [someExistsOneDivLT, dif_pos hi]
  -- ⊢ Classical.choose (_ : MeasureTheory.SignedMeasure.ExistsOneDivLT s i (Measur …
  exact Classical.choose_spec (findExistsOneDivLT_spec hi)
  -- 🎉 no goals

private theorem someExistsOneDivLT_subset : someExistsOneDivLT s i ⊆ i := by
  by_cases hi : ¬s ≤[i] 0
  -- ⊢ MeasureTheory.SignedMeasure.someExistsOneDivLT s i ⊆ i
  · exact
      let ⟨h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    -- ⊢ ∅ ⊆ i
    exact Set.empty_subset _
    -- 🎉 no goals

private theorem someExistsOneDivLT_subset' : someExistsOneDivLT s (i \ j) ⊆ i :=
  Set.Subset.trans someExistsOneDivLT_subset (Set.diff_subset _ _)

private theorem someExistsOneDivLT_measurableSet : MeasurableSet (someExistsOneDivLT s i) := by
  by_cases hi : ¬s ≤[i] 0
  -- ⊢ MeasurableSet (MeasureTheory.SignedMeasure.someExistsOneDivLT s i)
  · exact
      let ⟨_, h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    -- ⊢ MeasurableSet ∅
    exact MeasurableSet.empty
    -- 🎉 no goals

private theorem someExistsOneDivLT_lt (hi : ¬s ≤[i] 0) :
    (1 / (findExistsOneDivLT s i + 1) : ℝ) < s (someExistsOneDivLT s i) :=
  let ⟨_, _, h⟩ := someExistsOneDivLT_spec hi
  h

/-- Given the set `i`, `restrictNonposSeq s i` is the sequence of sets defined inductively where
`restrictNonposSeq s i 0 = someExistsOneDivLT s (i \ ∅)` and
`restrictNonposSeq s i (n + 1) = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq k)`.

For each `n : ℕ`,`s (restrictNonposSeq s i n)` is close to maximal among all subsets of
`i \ ⋃ k ≤ n, restrictNonposSeq s i k`. -/
private def restrictNonposSeq (s : SignedMeasure α) (i : Set α) : ℕ → Set α
  | 0 => someExistsOneDivLT s (i \ ∅) -- I used `i \ ∅` instead of `i` to simplify some proofs
  | n + 1 =>
    someExistsOneDivLT s
      (i \
        ⋃ (k) (H : k ≤ n),
          have : k < n + 1 := Nat.lt_succ_iff.mpr H
          restrictNonposSeq s i k)

private theorem restrictNonposSeq_succ (n : ℕ) :
    restrictNonposSeq s i n.succ = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) := by
  rw [restrictNonposSeq]
  -- 🎉 no goals

private theorem restrictNonposSeq_subset (n : ℕ) : restrictNonposSeq s i n ⊆ i := by
  cases n <;> · rw [restrictNonposSeq]; exact someExistsOneDivLT_subset'
  -- ⊢ MeasureTheory.SignedMeasure.restrictNonposSeq s i Nat.zero ⊆ i
                -- ⊢ MeasureTheory.SignedMeasure.someExistsOneDivLT s (i \ ∅) ⊆ i
                                        -- 🎉 no goals
                -- ⊢ MeasureTheory.SignedMeasure.someExistsOneDivLT s
                                        -- 🎉 no goals

private theorem restrictNonposSeq_lt (n : ℕ) (hn : ¬s ≤[i \ ⋃ k ≤ n, restrictNonposSeq s i k] 0) :
    (1 / (findExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) + 1) : ℝ) <
      s (restrictNonposSeq s i n.succ) := by
  rw [restrictNonposSeq_succ]
  -- ⊢ 1 / (↑(MeasureTheory.SignedMeasure.findExistsOneDivLT s (i \ ⋃ (k : ℕ) (_ :  …
  apply someExistsOneDivLT_lt hn
  -- 🎉 no goals

private theorem measure_of_restrictNonposSeq (hi₂ : ¬s ≤[i] 0) (n : ℕ)
    (hn : ¬s ≤[i \ ⋃ k < n, restrictNonposSeq s i k] 0) : 0 < s (restrictNonposSeq s i n) := by
  cases n with
  | zero =>
    rw [restrictNonposSeq]; rw [← @Set.diff_empty _ i] at hi₂
    rcases someExistsOneDivLT_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  | succ n =>
    rw [restrictNonposSeq_succ]
    have h₁ : ¬s ≤[i \ ⋃ (k : ℕ) (_ : k ≤ n), restrictNonposSeq s i k] 0 := by
      refine' mt (restrict_le_zero_subset _ _ (by simp [Nat.lt_succ_iff]; rfl)) hn
      convert measurable_of_not_restrict_le_zero _ hn using 3
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases someExistsOneDivLT_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h

private theorem restrictNonposSeq_measurableSet (n : ℕ) :
    MeasurableSet (restrictNonposSeq s i n) := by
  cases n <;>
  -- ⊢ MeasurableSet (MeasureTheory.SignedMeasure.restrictNonposSeq s i Nat.zero)
    · rw [restrictNonposSeq]
      -- ⊢ MeasurableSet (MeasureTheory.SignedMeasure.someExistsOneDivLT s (i \ ∅))
      -- ⊢ MeasurableSet
      -- 🎉 no goals
      exact someExistsOneDivLT_measurableSet
      -- 🎉 no goals

private theorem restrictNonposSeq_disjoint' {n m : ℕ} (h : n < m) :
    restrictNonposSeq s i n ∩ restrictNonposSeq s i m = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  -- ⊢ ∀ (x : α), ¬x ∈ MeasureTheory.SignedMeasure.restrictNonposSeq s i n ∩ Measur …
  rintro x ⟨hx₁, hx₂⟩
  -- ⊢ False
  cases m; · rw [Nat.zero_eq] at h; linarith
  -- ⊢ False
             -- ⊢ False
                                    -- 🎉 no goals
  · rw [restrictNonposSeq] at hx₂
    -- ⊢ False
    exact
      (someExistsOneDivLT_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Nat.lt_succ_iff.mp h, hx₁⟩⟩)

private theorem restrictNonposSeq_disjoint : Pairwise (Disjoint on restrictNonposSeq s i) := by
  intro n m h
  -- ⊢ (Disjoint on MeasureTheory.SignedMeasure.restrictNonposSeq s i) n m
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  -- ⊢ MeasureTheory.SignedMeasure.restrictNonposSeq s i n ∩ MeasureTheory.SignedMe …
  rcases lt_or_gt_of_ne h with (h | h)
  -- ⊢ MeasureTheory.SignedMeasure.restrictNonposSeq s i n ∩ MeasureTheory.SignedMe …
  · rw [restrictNonposSeq_disjoint' h]
    -- 🎉 no goals
  · rw [Set.inter_comm, restrictNonposSeq_disjoint' h]
    -- 🎉 no goals

private theorem exists_subset_restrict_nonpos' (hi₁ : MeasurableSet i) (hi₂ : s i < 0)
    (hn : ¬∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrictNonposSeq s i l] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 := by
  by_cases s ≤[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
                       -- 🎉 no goals
  push_neg at hn
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  set k := Nat.find hn
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  have hk₂ : s ≤[i \ ⋃ l < k, restrictNonposSeq s i l] 0 := Nat.find_spec hn
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  have hmeas : MeasurableSet (⋃ (l : ℕ) (_ : l < k), restrictNonposSeq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  refine' ⟨i \ ⋃ l < k, restrictNonposSeq s i l, hi₁.diff hmeas, Set.diff_subset _ _, hk₂, _⟩
  -- ⊢ ↑s (i \ ⋃ (l : ℕ) (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq …
  rw [of_diff hmeas hi₁, s.of_disjoint_iUnion_nat]
  · have h₁ : ∀ l < k, 0 ≤ s (restrictNonposSeq s i l) := by
      intro l hl
      refine' le_of_lt (measure_of_restrictNonposSeq h _ _)
      refine' mt (restrict_le_zero_subset _ (hi₁.diff _) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    suffices 0 ≤ ∑' l : ℕ, s (⋃ _ : l < k, restrictNonposSeq s i l) by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine' tsum_nonneg _
    -- ⊢ ∀ (i_1 : ℕ), 0 ≤ ↑s (⋃ (_ : i_1 < k), MeasureTheory.SignedMeasure.restrictNo …
    intro l; by_cases l < k
    -- ⊢ 0 ≤ ↑s (⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l)
             -- ⊢ 0 ≤ ↑s (⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l)
             -- ⊢ 0 ≤ ↑s (⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l)
    · convert h₁ _ h
      -- ⊢ ⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l = Measure …
      ext x
      -- ⊢ x ∈ ⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l ↔ x ∈ …
      rw [Set.mem_iUnion, exists_prop, and_iff_right_iff_imp]
      -- ⊢ x ∈ MeasureTheory.SignedMeasure.restrictNonposSeq s i l → l < k
      exact fun _ => h
      -- 🎉 no goals
    · convert le_of_eq s.empty.symm
      -- ⊢ ⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l = ∅
      ext; simp only [exists_prop, Set.mem_empty_iff_false, Set.mem_iUnion, not_and, iff_false_iff]
      -- ⊢ x✝ ∈ ⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i l ↔ x✝ …
           -- ⊢ l < Nat.find hn → ¬x✝ ∈ MeasureTheory.SignedMeasure.restrictNonposSeq s i l
      exact fun h' => False.elim (h h')
      -- 🎉 no goals
  · intro; exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    -- ⊢ MeasurableSet (⋃ (_ : i✝ < k), MeasureTheory.SignedMeasure.restrictNonposSeq …
           -- 🎉 no goals
  · intro a b hab
    -- ⊢ (Disjoint on fun l => ⋃ (_ : l < k), MeasureTheory.SignedMeasure.restrictNon …
    refine' Set.disjoint_iUnion_left.mpr fun _ => _
    -- ⊢ Disjoint (MeasureTheory.SignedMeasure.restrictNonposSeq s i a) ((fun l => ⋃  …
    refine' Set.disjoint_iUnion_right.mpr fun _ => _
    -- ⊢ Disjoint (MeasureTheory.SignedMeasure.restrictNonposSeq s i a) (MeasureTheor …
    exact restrictNonposSeq_disjoint hab
    -- 🎉 no goals
  · apply Set.iUnion_subset
    -- ⊢ ∀ (i_1 : ℕ), ⋃ (_ : i_1 < k), MeasureTheory.SignedMeasure.restrictNonposSeq  …
    intro a x
    -- ⊢ x ∈ ⋃ (_ : a < k), MeasureTheory.SignedMeasure.restrictNonposSeq s i a → x ∈ i
    simp only [and_imp, exists_prop, Set.mem_iUnion]
    -- ⊢ a < Nat.find hn → x ∈ MeasureTheory.SignedMeasure.restrictNonposSeq s i a →  …
    intro _ hx
    -- ⊢ x ∈ i
    exact restrictNonposSeq_subset _ hx
    -- 🎉 no goals

/-- A measurable set of negative measure has a negative subset of negative measure. -/
theorem exists_subset_restrict_nonpos (hi : s i < 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 := by
  have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi <| s.not_measurable h
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  by_cases s ≤[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
                       -- 🎉 no goals
  by_cases hn : ∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrictNonposSeq s i l] 0
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
          -- 🎉 no goals
  set A := i \ ⋃ l, restrictNonposSeq s i l with hA
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  set bdd : ℕ → ℕ := fun n => findExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k)
  -- ⊢ ∃ j, MeasurableSet j ∧ j ⊆ i ∧ restrict s j ≤ restrict 0 j ∧ ↑s j < 0
  have hn' : ∀ n : ℕ, ¬s ≤[i \ ⋃ l ≤ n, restrictNonposSeq s i l] 0 := by
    intro n
    convert hn (n + 1) using 5 <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => Nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrictNonposSeq s i l) := by
    rw [hA, ← s.of_disjoint_iUnion_nat, add_comm, of_add_of_diff]
    exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    exacts [hi₁, Set.iUnion_subset fun _ => restrictNonposSeq_subset _, fun _ =>
      restrictNonposSeq_measurableSet _, restrictNonposSeq_disjoint]
  have h₂ : s A ≤ s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrictNonposSeq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : ℝ) := by
    have : Summable fun l => s (restrictNonposSeq s i l) :=
      HasSum.summable
        (s.m_iUnion (fun _ => restrictNonposSeq_measurableSet _) restrictNonposSeq_disjoint)
    refine'
      summable_of_nonneg_of_le (fun n => _) (fun n => _)
        (Summable.comp_injective this Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrictNonposSeq_lt n (hn' n))
  have h₃ : Tendsto (fun n => (bdd n : ℝ) + 1) atTop atTop := by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : Tendsto (fun n => (bdd n : ℝ)) atTop atTop := by
    convert atTop.tendsto_atTop_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _)
  refine' ⟨A, A_meas, Set.diff_subset _ _, _, h₂.trans_lt hi⟩
  -- ⊢ restrict s A ≤ restrict 0 A
  by_contra hnn
  -- ⊢ False
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push_neg at hnn
  -- ⊢ False
                                                   -- ⊢ False
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  -- ⊢ False
  have : ∃ k, 1 ≤ bdd k ∧ 1 / (bdd k : ℝ) < s E := by
    rw [tendsto_atTop_atTop] at h₄
    obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1)
    refine' ⟨k, _, _⟩
    · have hle := le_of_max_le_right (hk k le_rfl)
      norm_cast at hle
    · have : 1 / s E < bdd k := by
        linarith only [le_of_max_le_left (hk k le_rfl)]
      rw [one_div] at this ⊢
      rwa [inv_lt (lt_trans (inv_pos.2 hE₃) this) hE₃]
  obtain ⟨k, hk₁, hk₂⟩ := this
  -- ⊢ False
  have hA' : A ⊆ i \ ⋃ l ≤ k, restrictNonposSeq s i l := by
    apply Set.diff_subset_diff_right
    intro x; simp only [Set.mem_iUnion]
    rintro ⟨n, _, hn₂⟩
    exact ⟨n, hn₂⟩
  refine'
    findExistsOneDivLT_min (hn' k) (Nat.sub_lt hk₁ Nat.zero_lt_one)
      ⟨E, Set.Subset.trans hE₂ hA', hE₁, _⟩
  convert hk₂; norm_cast
  -- ⊢ ↑(MeasureTheory.SignedMeasure.findExistsOneDivLT s (i \ ⋃ (l : ℕ) (_ : l ≤ k …
               -- ⊢ MeasureTheory.SignedMeasure.findExistsOneDivLT s (i \ ⋃ (l : ℕ) (_ : l ≤ k), …
  exact tsub_add_cancel_of_le hk₁
  -- 🎉 no goals
#align measure_theory.signed_measure.exists_subset_restrict_nonpos MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos

end ExistsSubsetRestrictNonpos

/-- The set of measures of the set of measurable negative sets. -/
def measureOfNegatives (s : SignedMeasure α) : Set ℝ :=
  s '' { B | MeasurableSet B ∧ s ≤[B] 0 }
#align measure_theory.signed_measure.measure_of_negatives MeasureTheory.SignedMeasure.measureOfNegatives

theorem zero_mem_measureOfNegatives : (0 : ℝ) ∈ s.measureOfNegatives :=
  ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩
#align measure_theory.signed_measure.zero_mem_measure_of_negatives MeasureTheory.SignedMeasure.zero_mem_measureOfNegatives

theorem bddBelow_measureOfNegatives : BddBelow s.measureOfNegatives := by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  -- ⊢ ∃ x, ∀ (x_1 : ℝ), x_1 ∈ measureOfNegatives s → x ≤ x_1
  by_contra' h
  -- ⊢ False
  have h' : ∀ n : ℕ, ∃ y : ℝ, y ∈ s.measureOfNegatives ∧ y < -n := fun n => h (-n)
  -- ⊢ False
  choose f hf using h'
  -- ⊢ False
  have hf' : ∀ n : ℕ, ∃ B, MeasurableSet B ∧ s ≤[B] 0 ∧ s B < -n := by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  -- ⊢ False
  set A := ⋃ n, B n with hA
  -- ⊢ False
  have hfalse : ∀ n : ℕ, s A ≤ -n := by
    intro n
    refine' le_trans _ (le_of_lt (h_lt _))
    rw [hA, ← Set.diff_union_of_subset (Set.subset_iUnion _ n),
      of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine' add_le_of_nonpos_left _
      have : s ≤[A] 0 := restrict_le_restrict_iUnion _ _ hmeas hr
      refine' nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (Set.diff_subset _ _) this)
      exact MeasurableSet.iUnion hmeas
    · exact (MeasurableSet.iUnion hmeas).diff (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  -- ⊢ False
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))
  -- 🎉 no goals
#align measure_theory.signed_measure.bdd_below_measure_of_negatives MeasureTheory.SignedMeasure.bddBelow_measureOfNegatives

/-- Alternative formulation of `measure_theory.signed_measure.exists_is_compl_positive_negative`
(the Hahn decomposition theorem) using set complements. -/
theorem exists_compl_positive_negative (s : SignedMeasure α) :
    ∃ i : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ s ≤[iᶜ] 0 := by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measureOfNegatives _ _ s⟩ bddBelow_measureOfNegatives
  choose B hB using hf₁
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  have hB₁ : ∀ n, MeasurableSet (B n) := fun n => (hB n).1.1
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  have hB₂ : ∀ n, s ≤[B n] 0 := fun n => (hB n).1.2
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  set A := ⋃ n, B n with hA
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  have hA₂ : s ≤[A] 0 := restrict_le_restrict_iUnion _ _ hB₁ hB₂
  -- ⊢ ∃ i, MeasurableSet i ∧ restrict 0 i ≤ restrict s i ∧ restrict s iᶜ ≤ restric …
  have hA₃ : s A = sInf s.measureOfNegatives := by
    apply le_antisymm
    · refine' le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (eventually_of_forall fun n => _)
      rw [← (hB n).2, hA, ← Set.diff_union_of_subset (Set.subset_iUnion _ n),
        of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine' add_le_of_nonpos_left _
        have : s ≤[A] 0 :=
          restrict_le_restrict_iUnion _ _ hB₁ fun m =>
            let ⟨_, h⟩ := (hB m).1
            h
        refine'
          nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (Set.diff_subset _ _) this)
        exact MeasurableSet.iUnion hB₁
      · exact (MeasurableSet.iUnion hB₁).diff (hB₁ n)
    · exact csInf_le bddBelow_measureOfNegatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩
  refine' ⟨Aᶜ, hA₁.compl, _, (compl_compl A).symm ▸ hA₂⟩
  -- ⊢ restrict 0 Aᶜ ≤ restrict s Aᶜ
  rw [restrict_le_restrict_iff _ _ hA₁.compl]
  -- ⊢ ∀ ⦃j : Set α⦄, MeasurableSet j → j ⊆ Aᶜ → ↑0 j ≤ ↑s j
  intro C _ hC₁
  -- ⊢ ↑0 C ≤ ↑s C
  by_contra' hC₂
  -- ⊢ False
  rcases exists_subset_restrict_nonpos hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩
  -- ⊢ False
  have : s (A ∪ D) < sInf s.measureOfNegatives := by
    rw [← hA₃,
      of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith
  refine' not_le.2 this _
  -- ⊢ sInf (measureOfNegatives s) ≤ ↑s (A ∪ D)
  refine' csInf_le bddBelow_measureOfNegatives ⟨A ∪ D, ⟨_, _⟩, rfl⟩
  -- ⊢ MeasurableSet (A ∪ D)
  · exact hA₁.union hD₁
    -- 🎉 no goals
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂
    -- 🎉 no goals
#align measure_theory.signed_measure.exists_compl_positive_negative MeasureTheory.SignedMeasure.exists_compl_positive_negative

/-- **The Hahn decomposition theorem**: Given a signed measure `s`, there exist
complement measurable sets `i` and `j` such that `i` is positive, `j` is negative. -/
theorem exists_isCompl_positive_negative (s : SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ MeasurableSet j ∧ s ≤[j] 0 ∧ IsCompl i j :=
  let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩
#align measure_theory.signed_measure.exists_is_compl_positive_negative MeasureTheory.SignedMeasure.exists_isCompl_positive_negative

/-- The symmetric difference of two Hahn decompositions has measure zero. -/
theorem of_symmDiff_compl_positive_negative {s : SignedMeasure α} {i j : Set α}
    (hi : MeasurableSet i) (hj : MeasurableSet j) (hi' : 0 ≤[i] s ∧ s ≤[iᶜ] 0)
    (hj' : 0 ≤[j] s ∧ s ≤[jᶜ] 0) : s (i ∆ j) = 0 ∧ s (iᶜ ∆ jᶜ) = 0 := by
  rw [restrict_le_restrict_iff s 0, restrict_le_restrict_iff 0 s] at hi' hj'
  constructor
  · rw [Set.symmDiff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, of_union,
      le_antisymm (hi'.2 (hi.compl.inter hj) (Set.inter_subset_left _ _))
        (hj'.1 (hi.compl.inter hj) (Set.inter_subset_right _ _)),
      le_antisymm (hj'.2 (hj.compl.inter hi) (Set.inter_subset_left _ _))
        (hi'.1 (hj.compl.inter hi) (Set.inter_subset_right _ _)),
      zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
          (Set.disjoint_of_subset_right (Set.inter_subset_right _ _)
            (disjoint_comm.1 (IsCompl.disjoint isCompl_compl)))
    · exact hj.compl.inter hi
      -- 🎉 no goals
    · exact hi.compl.inter hj
      -- 🎉 no goals
  · rw [Set.symmDiff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, compl_compl,
      compl_compl, of_union,
      le_antisymm (hi'.2 (hj.inter hi.compl) (Set.inter_subset_right _ _))
        (hj'.1 (hj.inter hi.compl) (Set.inter_subset_left _ _)),
      le_antisymm (hj'.2 (hi.inter hj.compl) (Set.inter_subset_right _ _))
        (hi'.1 (hi.inter hj.compl) (Set.inter_subset_left _ _)),
      zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
          (Set.disjoint_of_subset_right (Set.inter_subset_right _ _)
            (IsCompl.disjoint isCompl_compl))
    · exact hj.inter hi.compl
      -- 🎉 no goals
    · exact hi.inter hj.compl
      -- 🎉 no goals
  all_goals measurability
  -- 🎉 no goals
#align measure_theory.signed_measure.of_symm_diff_compl_positive_negative MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative

end SignedMeasure

end MeasureTheory
