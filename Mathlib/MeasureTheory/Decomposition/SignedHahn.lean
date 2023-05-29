/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module measure_theory.decomposition.signed_hahn
! leanprover-community/mathlib commit bc7d81beddb3d6c66f71449c5bc76c38cb77cf9e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.VectorMeasure
import Mathbin.Order.SymmDiff

/-!
# Hahn decomposition

This file proves the Hahn decomposition theorem (signed version). The Hahn decomposition theorem
states that, given a signed measure `s`, there exist complementary, measurable sets `i` and `j`,
such that `i` is positive and `j` is negative with respect to `s`; that is, `s` restricted on `i`
is non-negative and `s` restricted on `j` is non-positive.

The Hahn decomposition theorem leads to many other results in measure theory, most notably,
the Jordan decomposition theorem, the Lebesgue decomposition theorem and the Radon-Nikodym theorem.

## Main results

* `measure_theory.signed_measure.exists_is_compl_positive_negative` : the Hahn decomposition
  theorem.
* `measure_theory.signed_measure.exists_subset_restrict_nonpos` : A measurable set of negative
  measure contains a negative subset.

## Notation

We use the notations `0 ≤[i] s` and `s ≤[i] 0` to denote the usual definitions of a set `i`
being positive/negative with respect to the signed measure `s`.

## Tags

Hahn decomposition theorem
-/


noncomputable section

open scoped Classical BigOperators NNReal ENNReal MeasureTheory

variable {α β : Type _} [MeasurableSpace α]

variable {M : Type _} [AddCommMonoid M] [TopologicalSpace M] [OrderedAddCommMonoid M]

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

To implement this in Lean, we define several auxilary definitions.

- given the sets `i` and the natural number `n`, `exists_one_div_lt s i n` is the property that
  there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`.
- given the sets `i` and that `i` is not negative, `find_exists_one_div_lt s i` is the
  least natural number `n` such that `exists_one_div_lt s i n`.
- given the sets `i` and that `i` is not negative, `some_exists_one_div_lt` chooses the set
  `k` from `exists_one_div_lt s i (find_exists_one_div_lt s i)`.
- lastly, given the set `i`, `restrict_nonpos_seq s i` is the sequence of sets defined inductively
  where
  `restrict_nonpos_seq s i 0 = some_exists_one_div_lt s (i \ ∅)` and
  `restrict_nonpos_seq s i (n + 1) = some_exists_one_div_lt s (i \ ⋃ k ≤ n, restrict_nonpos_seq k)`.
  This definition represents the sequence $(A_n)$ in the proof as described above.

With these definitions, we are able consider the case where the sequence terminates separately,
allowing us to prove `exists_subset_restrict_nonpos`.
-/


/-- Given the set `i` and the natural number `n`, `exists_one_div_lt s i j` is the property that
there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`. -/
private def exists_one_div_lt (s : SignedMeasure α) (i : Set α) (n : ℕ) : Prop :=
  ∃ k : Set α, k ⊆ i ∧ MeasurableSet k ∧ (1 / (n + 1) : ℝ) < s k

private theorem exists_nat_one_div_lt_measure_of_not_negative (hi : ¬s ≤[i] 0) :
    ∃ n : ℕ, ExistsOneDivLt s i n :=
  let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

/-- Given the set `i`, if `i` is not negative, `find_exists_one_div_lt s i` is the
least natural number `n` such that `exists_one_div_lt s i n`, otherwise, it returns 0. -/
private def find_exists_one_div_lt (s : SignedMeasure α) (i : Set α) : ℕ :=
  if hi : ¬s ≤[i] 0 then Nat.find (exists_nat_one_div_lt_measure_of_not_negative hi) else 0

private theorem find_exists_one_div_lt_spec (hi : ¬s ≤[i] 0) :
    ExistsOneDivLt s i (findExistsOneDivLt s i) :=
  by
  rw [find_exists_one_div_lt, dif_pos hi]
  convert Nat.find_spec _

private theorem find_exists_one_div_lt_min (hi : ¬s ≤[i] 0) {m : ℕ}
    (hm : m < findExistsOneDivLt s i) : ¬ExistsOneDivLt s i m :=
  by
  rw [find_exists_one_div_lt, dif_pos hi] at hm
  exact Nat.find_min _ hm

/-- Given the set `i`, if `i` is not negative, `some_exists_one_div_lt` chooses the set
`k` from `exists_one_div_lt s i (find_exists_one_div_lt s i)`, otherwise, it returns the
empty set. -/
private def some_exists_one_div_lt (s : SignedMeasure α) (i : Set α) : Set α :=
  if hi : ¬s ≤[i] 0 then Classical.choose (findExistsOneDivLt_spec hi) else ∅

private theorem some_exists_one_div_lt_spec (hi : ¬s ≤[i] 0) :
    someExistsOneDivLt s i ⊆ i ∧
      MeasurableSet (someExistsOneDivLt s i) ∧
        (1 / (findExistsOneDivLt s i + 1) : ℝ) < s (someExistsOneDivLt s i) :=
  by
  rw [some_exists_one_div_lt, dif_pos hi]
  exact Classical.choose_spec (find_exists_one_div_lt_spec hi)

private theorem some_exists_one_div_lt_subset : someExistsOneDivLt s i ⊆ i :=
  by
  by_cases hi : ¬s ≤[i] 0
  ·
    exact
      let ⟨h, _⟩ := some_exists_one_div_lt_spec hi
      h
  · rw [some_exists_one_div_lt, dif_neg hi]
    exact Set.empty_subset _

private theorem some_exists_one_div_lt_subset' : someExistsOneDivLt s (i \ j) ⊆ i :=
  Set.Subset.trans someExistsOneDivLt_subset (Set.diff_subset _ _)

private theorem some_exists_one_div_lt_measurable_set : MeasurableSet (someExistsOneDivLt s i) :=
  by
  by_cases hi : ¬s ≤[i] 0
  ·
    exact
      let ⟨_, h, _⟩ := some_exists_one_div_lt_spec hi
      h
  · rw [some_exists_one_div_lt, dif_neg hi]
    exact MeasurableSet.empty

private theorem some_exists_one_div_lt_lt (hi : ¬s ≤[i] 0) :
    (1 / (findExistsOneDivLt s i + 1) : ℝ) < s (someExistsOneDivLt s i) :=
  let ⟨_, _, h⟩ := someExistsOneDivLt_spec hi
  h

/-- Given the set `i`, `restrict_nonpos_seq s i` is the sequence of sets defined inductively where
`restrict_nonpos_seq s i 0 = some_exists_one_div_lt s (i \ ∅)` and
`restrict_nonpos_seq s i (n + 1) = some_exists_one_div_lt s (i \ ⋃ k ≤ n, restrict_nonpos_seq k)`.

For each `n : ℕ`,`s (restrict_nonpos_seq s i n)` is close to maximal among all subsets of
`i \ ⋃ k ≤ n, restrict_nonpos_seq s i k`. -/
private def restrict_nonpos_seq (s : SignedMeasure α) (i : Set α) : ℕ → Set α
  | 0 => someExistsOneDivLt s (i \ ∅)
  |-- I used `i \ ∅` instead of `i` to simplify some proofs
      n +
      1 =>
    someExistsOneDivLt s
      (i \
        ⋃ k ≤ n,
          have : k < n + 1 := Nat.lt_succ_iff.mpr H
          restrict_nonpos_seq k)

private theorem restrict_nonpos_seq_succ (n : ℕ) :
    restrictNonposSeq s i n.succ = someExistsOneDivLt s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) := by
  rw [restrict_nonpos_seq]

private theorem restrict_nonpos_seq_subset (n : ℕ) : restrictNonposSeq s i n ⊆ i := by
  cases n <;> · rw [restrict_nonpos_seq]; exact some_exists_one_div_lt_subset'

private theorem restrict_nonpos_seq_lt (n : ℕ) (hn : ¬s ≤[i \ ⋃ k ≤ n, restrictNonposSeq s i k] 0) :
    (1 / (findExistsOneDivLt s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) + 1) : ℝ) <
      s (restrictNonposSeq s i n.succ) :=
  by
  rw [restrict_nonpos_seq_succ]
  apply some_exists_one_div_lt_lt hn

private theorem measure_of_restrict_nonpos_seq (hi₂ : ¬s ≤[i] 0) (n : ℕ)
    (hn : ¬s ≤[i \ ⋃ k < n, restrictNonposSeq s i k] 0) : 0 < s (restrictNonposSeq s i n) :=
  by
  cases n
  · rw [restrict_nonpos_seq]; rw [← @Set.diff_empty _ i] at hi₂
    rcases some_exists_one_div_lt_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  · rw [restrict_nonpos_seq_succ]
    have h₁ : ¬s ≤[i \ ⋃ (k : ℕ) (H : k ≤ n), restrict_nonpos_seq s i k] 0 :=
      by
      refine' mt (restrict_le_zero_subset _ _ (by simp [Nat.lt_succ_iff])) hn
      convert measurable_of_not_restrict_le_zero _ hn
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases some_exists_one_div_lt_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h

private theorem restrict_nonpos_seq_measurable_set (n : ℕ) :
    MeasurableSet (restrictNonposSeq s i n) := by
  cases n <;>
    · rw [restrict_nonpos_seq]
      exact some_exists_one_div_lt_measurable_set

private theorem restrict_nonpos_seq_disjoint' {n m : ℕ} (h : n < m) :
    restrictNonposSeq s i n ∩ restrictNonposSeq s i m = ∅ :=
  by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro x ⟨hx₁, hx₂⟩
  cases m; · linarith
  · rw [restrict_nonpos_seq] at hx₂
    exact
      (some_exists_one_div_lt_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨nat.lt_succ_iff.mp h, hx₁⟩⟩)

private theorem restrict_nonpos_seq_disjoint : Pairwise (Disjoint on restrictNonposSeq s i) :=
  by
  intro n m h
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne h with (h | h)
  · rw [restrict_nonpos_seq_disjoint' h]
  · rw [Set.inter_comm, restrict_nonpos_seq_disjoint' h]

private theorem exists_subset_restrict_nonpos' (hi₁ : MeasurableSet i) (hi₂ : s i < 0)
    (hn : ¬∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrictNonposSeq s i l] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 :=
  by
  by_cases s ≤[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  push_neg  at hn
  set k := Nat.find hn with hk₁
  have hk₂ : s ≤[i \ ⋃ l < k, restrict_nonpos_seq s i l] 0 := Nat.find_spec hn
  have hmeas : MeasurableSet (⋃ (l : ℕ) (H : l < k), restrict_nonpos_seq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrict_nonpos_seq_measurable_set _
  refine' ⟨i \ ⋃ l < k, restrict_nonpos_seq s i l, hi₁.diff hmeas, Set.diff_subset _ _, hk₂, _⟩
  rw [of_diff hmeas hi₁, s.of_disjoint_Union_nat]
  · have h₁ : ∀ l < k, 0 ≤ s (restrict_nonpos_seq s i l) :=
      by
      intro l hl
      refine' le_of_lt (measure_of_restrict_nonpos_seq h _ _)
      refine' mt (restrict_le_zero_subset _ (hi₁.diff _) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrict_nonpos_seq_measurable_set _
    suffices 0 ≤ ∑' l : ℕ, s (⋃ H : l < k, restrict_nonpos_seq s i l)
      by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine' tsum_nonneg _
    intro l; by_cases l < k
    · convert h₁ _ h
      ext x
      rw [Set.mem_iUnion, exists_prop, and_iff_right_iff_imp]
      exact fun _ => h
    · convert le_of_eq s.empty.symm
      ext; simp only [exists_prop, Set.mem_empty_iff_false, Set.mem_iUnion, not_and, iff_false_iff]
      exact fun h' => False.elim (h h')
  · intro ; exact MeasurableSet.iUnion fun _ => restrict_nonpos_seq_measurable_set _
  · intro a b hab
    refine' set.disjoint_Union_left.mpr fun ha => _
    refine' set.disjoint_Union_right.mpr fun hb => _
    exact restrict_nonpos_seq_disjoint hab
  · apply Set.iUnion_subset
    intro a x
    simp only [and_imp, exists_prop, Set.mem_iUnion]
    intro _ hx
    exact restrict_nonpos_seq_subset _ hx
  · infer_instance

/-- A measurable set of negative measure has a negative subset of negative measure. -/
theorem exists_subset_restrict_nonpos (hi : s i < 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 :=
  by
  have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi <| s.not_measurable h
  by_cases s ≤[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  by_cases hn : ∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrict_nonpos_seq s i l] 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  set A := i \ ⋃ l, restrict_nonpos_seq s i l with hA
  set bdd : ℕ → ℕ := fun n => find_exists_one_div_lt s (i \ ⋃ k ≤ n, restrict_nonpos_seq s i k) with
    hbdd
  have hn' : ∀ n : ℕ, ¬s ≤[i \ ⋃ l ≤ n, restrict_nonpos_seq s i l] 0 :=
    by
    intro n
    convert hn (n + 1) <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrict_nonpos_seq s i l) :=
    by
    rw [hA, ← s.of_disjoint_Union_nat, add_comm, of_add_of_diff]
    exact MeasurableSet.iUnion fun _ => restrict_nonpos_seq_measurable_set _
    exacts[hi₁, Set.iUnion_subset fun _ => restrict_nonpos_seq_subset _, fun _ =>
      restrict_nonpos_seq_measurable_set _, restrict_nonpos_seq_disjoint]
  have h₂ : s A ≤ s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrict_nonpos_seq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : ℝ) :=
    by
    have : Summable fun l => s (restrict_nonpos_seq s i l) :=
      HasSum.summable
        (s.m_Union (fun _ => restrict_nonpos_seq_measurable_set _) restrict_nonpos_seq_disjoint)
    refine'
      summable_of_nonneg_of_le (fun n => _) (fun n => _)
        (Summable.comp_injective this Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrict_nonpos_seq_lt n (hn' n))
  have h₃ : tendsto (fun n => (bdd n : ℝ) + 1) at_top at_top :=
    by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : tendsto (fun n => (bdd n : ℝ)) at_top at_top := by
    convert at_top.tendsto_at_top_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrict_nonpos_seq_measurable_set _)
  refine' ⟨A, A_meas, Set.diff_subset _ _, _, h₂.trans_lt hi⟩
  by_contra hnn
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push_neg  at hnn
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  have : ∃ k, 1 ≤ bdd k ∧ 1 / (bdd k : ℝ) < s E :=
    by
    rw [tendsto_at_top_at_top] at h₄
    obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1)
    refine' ⟨k, _, _⟩
    · have hle := le_of_max_le_right (hk k le_rfl)
      norm_cast  at hle
      exact hle
    · have : 1 / s E < bdd k := by
        linarith (config := { restrict_type := ℝ }) [le_of_max_le_left (hk k le_rfl)]
      rw [one_div] at this⊢
      rwa [inv_lt (lt_trans (inv_pos.2 hE₃) this) hE₃]
  obtain ⟨k, hk₁, hk₂⟩ := this
  have hA' : A ⊆ i \ ⋃ l ≤ k, restrict_nonpos_seq s i l :=
    by
    apply Set.diff_subset_diff_right
    intro x; simp only [Set.mem_iUnion]
    rintro ⟨n, _, hn₂⟩
    exact ⟨n, hn₂⟩
  refine'
    find_exists_one_div_lt_min (hn' k) (Buffer.lt_aux_2 hk₁) ⟨E, Set.Subset.trans hE₂ hA', hE₁, _⟩
  convert hk₂; norm_cast
  exact tsub_add_cancel_of_le hk₁
#align measure_theory.signed_measure.exists_subset_restrict_nonpos MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos

end ExistsSubsetRestrictNonpos

/-- The set of measures of the set of measurable negative sets. -/
def measureOfNegatives (s : SignedMeasure α) : Set ℝ :=
  s '' { B | MeasurableSet B ∧ s ≤[B] 0 }
#align measure_theory.signed_measure.measure_of_negatives MeasureTheory.SignedMeasure.measureOfNegatives

theorem zero_mem_measureOfNegatives : (0 : ℝ) ∈ s.measureOfNegatives :=
  ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.Empty⟩
#align measure_theory.signed_measure.zero_mem_measure_of_negatives MeasureTheory.SignedMeasure.zero_mem_measureOfNegatives

theorem bddBelow_measureOfNegatives : BddBelow s.measureOfNegatives :=
  by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  by_contra' h
  have h' : ∀ n : ℕ, ∃ y : ℝ, y ∈ s.measure_of_negatives ∧ y < -n := fun n => h (-n)
  choose f hf using h'
  have hf' : ∀ n : ℕ, ∃ B, MeasurableSet B ∧ s ≤[B] 0 ∧ s B < -n :=
    by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  set A := ⋃ n, B n with hA
  have hfalse : ∀ n : ℕ, s A ≤ -n := by
    intro n
    refine' le_trans _ (le_of_lt (h_lt _))
    rw [hA, ← Set.diff_union_of_subset (Set.subset_iUnion _ n),
      of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine' add_le_of_nonpos_left _
      have : s ≤[A] 0 := restrict_le_restrict_Union _ _ hmeas hr
      refine' nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (Set.diff_subset _ _) this)
      exact MeasurableSet.iUnion hmeas
    · infer_instance
    · exact (MeasurableSet.iUnion hmeas).diffₓ (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))
#align measure_theory.signed_measure.bdd_below_measure_of_negatives MeasureTheory.SignedMeasure.bddBelow_measureOfNegatives

/-- Alternative formulation of `measure_theory.signed_measure.exists_is_compl_positive_negative`
(the Hahn decomposition theorem) using set complements. -/
theorem exists_compl_positive_negative (s : SignedMeasure α) :
    ∃ i : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ s ≤[iᶜ] 0 :=
  by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measure_of_negatives _ _ s⟩ bdd_below_measure_of_negatives
  choose B hB using hf₁
  have hB₁ : ∀ n, MeasurableSet (B n) := fun n => (hB n).1.1
  have hB₂ : ∀ n, s ≤[B n] 0 := fun n => (hB n).1.2
  set A := ⋃ n, B n with hA
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  have hA₂ : s ≤[A] 0 := restrict_le_restrict_Union _ _ hB₁ hB₂
  have hA₃ : s A = Inf s.measure_of_negatives :=
    by
    apply le_antisymm
    · refine' le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (eventually_of_forall fun n => _)
      rw [← (hB n).2, hA, ← Set.diff_union_of_subset (Set.subset_iUnion _ n),
        of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine' add_le_of_nonpos_left _
        have : s ≤[A] 0 :=
          restrict_le_restrict_Union _ _ hB₁ fun m =>
            let ⟨_, h⟩ := (hB m).1
            h
        refine'
          nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (Set.diff_subset _ _) this)
        exact MeasurableSet.iUnion hB₁
      · infer_instance
      · exact (MeasurableSet.iUnion hB₁).diffₓ (hB₁ n)
    · exact csInf_le bdd_below_measure_of_negatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩
  refine' ⟨Aᶜ, hA₁.compl, _, (compl_compl A).symm ▸ hA₂⟩
  rw [restrict_le_restrict_iff _ _ hA₁.compl]
  intro C hC hC₁
  by_contra' hC₂
  rcases exists_subset_restrict_nonpos hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩
  have : s (A ∪ D) < Inf s.measure_of_negatives :=
    by
    rw [← hA₃,
      of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith; infer_instance
  refine' not_le.2 this _
  refine' csInf_le bdd_below_measure_of_negatives ⟨A ∪ D, ⟨_, _⟩, rfl⟩
  · exact hA₁.union hD₁
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂
#align measure_theory.signed_measure.exists_compl_positive_negative MeasureTheory.SignedMeasure.exists_compl_positive_negative

/-- **The Hahn decomposition thoerem**: Given a signed measure `s`, there exist
complement measurable sets `i` and `j` such that `i` is positive, `j` is negative. -/
theorem exists_isCompl_positive_negative (s : SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ MeasurableSet j ∧ s ≤[j] 0 ∧ IsCompl i j :=
  let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩
#align measure_theory.signed_measure.exists_is_compl_positive_negative MeasureTheory.SignedMeasure.exists_isCompl_positive_negative

/-- The symmetric difference of two Hahn decompositions has measure zero. -/
theorem of_symmDiff_compl_positive_negative {s : SignedMeasure α} {i j : Set α}
    (hi : MeasurableSet i) (hj : MeasurableSet j) (hi' : 0 ≤[i] s ∧ s ≤[iᶜ] 0)
    (hj' : 0 ≤[j] s ∧ s ≤[jᶜ] 0) : s (i ∆ j) = 0 ∧ s (iᶜ ∆ jᶜ) = 0 :=
  by
  rw [restrict_le_restrict_iff s 0, restrict_le_restrict_iff 0 s] at hi' hj'
  constructor
  · rw [symmDiff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, Set.sup_eq_union, of_union,
      le_antisymm (hi'.2 (hi.compl.inter hj) (Set.inter_subset_left _ _))
        (hj'.1 (hi.compl.inter hj) (Set.inter_subset_right _ _)),
      le_antisymm (hj'.2 (hj.compl.inter hi) (Set.inter_subset_left _ _))
        (hi'.1 (hj.compl.inter hi) (Set.inter_subset_right _ _)),
      zero_apply, zero_apply, zero_add]
    ·
      exact
        Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
          (Set.disjoint_of_subset_right (Set.inter_subset_right _ _)
            (disjoint_comm.1 (IsCompl.disjoint isCompl_compl)))
    · exact hj.compl.inter hi
    · exact hi.compl.inter hj
  · rw [symmDiff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, compl_compl, compl_compl,
      Set.sup_eq_union, of_union,
      le_antisymm (hi'.2 (hj.inter hi.compl) (Set.inter_subset_right _ _))
        (hj'.1 (hj.inter hi.compl) (Set.inter_subset_left _ _)),
      le_antisymm (hj'.2 (hi.inter hj.compl) (Set.inter_subset_right _ _))
        (hi'.1 (hi.inter hj.compl) (Set.inter_subset_left _ _)),
      zero_apply, zero_apply, zero_add]
    ·
      exact
        Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
          (Set.disjoint_of_subset_right (Set.inter_subset_right _ _)
            (IsCompl.disjoint isCompl_compl))
    · exact hj.inter hi.compl
    · exact hi.inter hj.compl
  all_goals measurability
#align measure_theory.signed_measure.of_symm_diff_compl_positive_negative MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative

end SignedMeasure

end MeasureTheory

