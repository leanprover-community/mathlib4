/-
Copyright (c) 2022 Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kexing Ying
-/
import Mathlib.Probability.CondCount

#align_import wiedijk_100_theorems.ballot_problem from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
# Ballot problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The ballot problem asks, if in an election, candidate A receives `p` votes whereas candidate B
receives `q` votes where `p > q`, what is the probability that candidate A is strictly ahead
throughout the count. The probability of this is `(p - q) / (p + q)`.

## Main definitions

* `countedSequence`: given natural numbers `p` and `q`, `countedSequence p q` is the set of
  all lists containing `p` of `1`s and `q` of `-1`s representing the votes of candidate A and B
  respectively.
* `staysPositive`: is the set of lists of integers which suffix has positive sum. In particular,
  the intersection of this set with `countedSequence` is the set of lists where candidate A is
  strictly ahead.

## Main result

* `ballot_problem`: the ballot problem.

-/


open Set ProbabilityTheory MeasureTheory
open scoped ENNReal

namespace Ballot

/-- The set of nonempty lists of integers which suffix has positive sum. -/
def staysPositive : Set (List ℤ) :=
  {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}
#align ballot.stays_positive Ballot.staysPositive

@[simp]
theorem staysPositive_nil : [] ∈ staysPositive :=
  fun _ hl hl₁ => (hl (List.eq_nil_of_suffix_nil hl₁)).elim
#align ballot.stays_positive_nil Ballot.staysPositive_nil

theorem staysPositive_suffix {l₁ l₂ : List ℤ} (hl₂ : l₂ ∈ staysPositive) (h : l₁ <:+ l₂) :
    l₁ ∈ staysPositive := fun l hne hl ↦ hl₂ l hne <| hl.trans h

theorem staysPositive_cons {x : ℤ} {l : List ℤ} :
    x::l ∈ staysPositive ↔ l ∈ staysPositive ∧ 0 < x + l.sum := by
  simp [staysPositive, List.suffix_cons_iff, or_imp, forall_and, @imp.swap _ (_ = _), and_comm]

theorem sum_nonneg_of_staysPositive : ∀ {l : List ℤ}, l ∈ staysPositive → 0 ≤ l.sum
  | [], _ => le_rfl
  | (_::_), h => (h _ (List.cons_ne_nil _ _) (List.suffix_refl _)).le

theorem staysPositive_cons_pos (x : ℤ) (hx : 0 < x) (l : List ℤ) :
    (x::l) ∈ staysPositive ↔ l ∈ staysPositive := by
  rw [staysPositive_cons, and_iff_left_iff_imp]
  intro h
  have := sum_nonneg_of_staysPositive h
  positivity
#align ballot.stays_positive_cons_pos Ballot.staysPositive_cons_pos

/-- `countedSequence p q` is the set of lists of integers for which every element is `+1` or `-1`,
there are `p` lots of `+1` and `q` lots of `-1`.

This represents vote sequences where candidate `+1` receives `p` votes and candidate `-1` receives
`q` votes.
-/
def countedSequence (p q : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}
#align ballot.counted_sequence Ballot.countedSequence

open scoped List in
/-- An alternative definition of `countedSequence` that uses `List.Perm`. -/
theorem mem_countedSequence_iff_perm {p q l} :
    l ∈ countedSequence p q ↔ l ~ List.replicate p (1 : ℤ) ++ List.replicate q (-1) := by
  rw [List.perm_replicate_append_replicate]
  · simp only [countedSequence, List.subset_def, mem_setOf_eq, List.mem_cons (b := (1 : ℤ)),
      List.mem_singleton]
  · norm_num1
#align ballot.mem_counted_sequence_iff_perm Ballot.mem_countedSequence_iff_perm

@[simp]
theorem counted_right_zero (p : ℕ) : countedSequence p 0 = {List.replicate p 1} := by
  ext l; simp [mem_countedSequence_iff_perm]
#align ballot.counted_right_zero Ballot.counted_right_zero

@[simp]
theorem counted_left_zero (q : ℕ) : countedSequence 0 q = {List.replicate q (-1)} := by
  ext l; simp [mem_countedSequence_iff_perm]
#align ballot.counted_left_zero Ballot.counted_left_zero

theorem mem_of_mem_countedSequence {p q} {l} (hl : l ∈ countedSequence p q) {x : ℤ} (hx : x ∈ l) :
    x = 1 ∨ x = -1 :=
  hl.2.2 x hx
#align ballot.mem_of_mem_counted_sequence Ballot.mem_of_mem_countedSequence

theorem length_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.length = p + q := by simp [(mem_countedSequence_iff_perm.1 hl).length_eq]
#align ballot.length_of_mem_counted_sequence Ballot.length_of_mem_countedSequence

theorem counted_eq_nil_iff {p q : ℕ} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l = [] ↔ p = 0 ∧ q = 0 :=
  List.length_eq_zero.symm.trans <| by simp [length_of_mem_countedSequence hl]
#align ballot.counted_eq_nil_iff Ballot.counted_eq_nil_iff

theorem counted_ne_nil_left {p q : ℕ} (hp : p ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hp]
#align ballot.counted_ne_nil_left Ballot.counted_ne_nil_left

theorem counted_ne_nil_right {p q : ℕ} (hq : q ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hq]
#align ballot.counted_ne_nil_right Ballot.counted_ne_nil_right

theorem counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) =
      List.cons 1 '' countedSequence p (q + 1) ∪ List.cons (-1) '' countedSequence (p + 1) q := by
  ext l
  rw [countedSequence, countedSequence, countedSequence]
  constructor
  · intro hl
    have hlnil := counted_ne_nil_left (Nat.succ_ne_zero p) hl
    obtain ⟨hl₀, hl₁, hl₂⟩ := hl
    obtain hlast | hlast := hl₂ (l.head hlnil) (List.head_mem hlnil)
    · refine Or.inl ⟨l.tail, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.count_tail l 1 hlnil, hl₀, hlast, if_pos rfl, Nat.add_sub_cancel]
      · rw [List.count_tail l (-1) hlnil, hl₁, hlast, if_neg (by decide), Nat.sub_zero]
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.head_cons_tail]
    · refine Or.inr ⟨l.tail, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.count_tail l 1 hlnil, hl₀, hlast, if_neg (by decide), Nat.sub_zero]
      · rw [List.count_tail l (-1) hlnil, hl₁, hlast, if_pos rfl, Nat.add_sub_cancel]
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.head_cons_tail]
  · rintro (⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩ | ⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩)
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.count_cons, if_pos rfl, ht₀]
      · rw [List.count_cons, if_neg, ht₁]
        norm_num
      · rintro x (_ | _)
        exacts [Or.inl rfl, ht₂ x (by tauto)]
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.count_cons, if_neg, ht₀]
        norm_num
      · rw [List.count_cons, if_pos rfl, ht₁]
      · rintro x (_ | _)
        exacts [Or.inr rfl, ht₂ x (by tauto)]
#align ballot.counted_succ_succ Ballot.counted_succ_succ

theorem countedSequence_finite : ∀ p q : ℕ, (countedSequence p q).Finite
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, Set.finite_union, Set.finite_image_iff List.cons_injective.injOn,
      Set.finite_image_iff List.cons_injective.injOn]
    exact ⟨countedSequence_finite _ _, countedSequence_finite _ _⟩
#align ballot.counted_sequence_finite Ballot.countedSequence_finite

theorem countedSequence_nonempty : ∀ p q : ℕ, (countedSequence p q).Nonempty
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, union_nonempty, image_nonempty]
    exact Or.inl (countedSequence_nonempty _ _)
#align ballot.counted_sequence_nonempty Ballot.countedSequence_nonempty

theorem sum_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.sum = p - q := by simp [(mem_countedSequence_iff_perm.1 hl).sum_eq, sub_eq_add_neg]
#align ballot.sum_of_mem_counted_sequence Ballot.sum_of_mem_countedSequence

theorem disjoint_bits (p q : ℕ) :
    Disjoint (List.cons 1 '' countedSequence p (q + 1))
      (List.cons (-1) '' countedSequence (p + 1) q) := by
  simp_rw [disjoint_left, mem_image, not_exists, exists_imp]
  rintro _ _ ⟨_, rfl⟩ _ ⟨_, _, _⟩
#align ballot.disjoint_bits Ballot.disjoint_bits

open MeasureTheory.Measure

private def measureableSpace_list_int : MeasurableSpace (List ℤ) := ⊤

attribute [local instance] measureableSpace_list_int

private theorem measurableSingletonClass_list_int : MeasurableSingletonClass (List ℤ) :=
  { measurableSet_singleton := fun _ => trivial }

attribute [local instance] measurableSingletonClass_list_int

private theorem list_int_measurableSet {s : Set (List ℤ)} : MeasurableSet s := trivial

theorem count_countedSequence : ∀ p q : ℕ, count (countedSequence p q) = (p + q).choose p
  | p, 0 => by simp [counted_right_zero, count_singleton]
  | 0, q => by simp [counted_left_zero, count_singleton]
  | p + 1, q + 1 => by
    rw [counted_succ_succ, measure_union (disjoint_bits _ _) list_int_measurableSet,
      count_injective_image List.cons_injective, count_countedSequence _ _,
      count_injective_image List.cons_injective, count_countedSequence _ _]
    norm_cast
    rw [add_assoc, add_comm 1 q, ← Nat.choose_succ_succ, Nat.succ_eq_add_one, add_right_comm]
#align ballot.count_counted_sequence Ballot.count_countedSequence

theorem first_vote_pos :
    ∀ p q,
      0 < p + q → condCount (countedSequence p q : Set (List ℤ)) {l | l.headI = 1} = p / (p + q)
  | p + 1, 0, _ => by
    rw [counted_right_zero, condCount_singleton]
    simp [ENNReal.div_self _ _]
  | 0, q + 1, _ => by
    rw [counted_left_zero, condCount_singleton]
    simp only [List.replicate, Nat.add_eq, add_zero, mem_setOf_eq, List.headI_cons, Nat.cast_zero,
      ENNReal.zero_div, ite_eq_right_iff]
    decide
  | p + 1, q + 1, _ => by
    simp_rw [counted_succ_succ]
    rw [← condCount_disjoint_union ((countedSequence_finite _ _).image _)
        ((countedSequence_finite _ _).image _) (disjoint_bits _ _),
      ← counted_succ_succ,
      condCount_eq_one_of ((countedSequence_finite p (q + 1)).image _)
        ((countedSequence_nonempty _ _).image _)]
    · have : List.cons (-1) '' countedSequence (p + 1) q ∩ {l : List ℤ | l.headI = 1} = ∅ := by
        ext
        simp only [mem_inter_iff, mem_image, mem_setOf_eq, mem_empty_iff_false, iff_false_iff,
          not_and, forall_exists_index, and_imp]
        rintro l _ rfl
        norm_num
      have hint :
        countedSequence (p + 1) (q + 1) ∩ List.cons 1 '' countedSequence p (q + 1) =
          List.cons 1 '' countedSequence p (q + 1) := by
        rw [inter_eq_right, counted_succ_succ]
        exact subset_union_left
      rw [(condCount_eq_zero_iff <| (countedSequence_finite _ _).image _).2 this, condCount,
        cond_apply _ list_int_measurableSet, hint, count_injective_image List.cons_injective,
        count_countedSequence, count_countedSequence, one_mul, zero_mul, add_zero,
        Nat.cast_add, Nat.cast_one, mul_comm, ← div_eq_mul_inv, ENNReal.div_eq_div_iff]
      · norm_cast
        rw [mul_comm _ (p + 1), ← Nat.succ_eq_add_one p, Nat.succ_add, Nat.succ_mul_choose_eq,
          mul_comm]
      all_goals simp [(Nat.choose_pos <| (le_add_iff_nonneg_right _).2 zero_le').ne.symm]
    · simp
#align ballot.first_vote_pos Ballot.first_vote_pos

theorem headI_mem_of_nonempty {α : Type*} [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), l.headI ∈ l
  | [], h => (h rfl).elim
  | x::l, _ => List.mem_cons_self x l
#align ballot.head_mem_of_nonempty Ballot.headI_mem_of_nonempty

theorem first_vote_neg (p q : ℕ) (h : 0 < p + q) :
    condCount (countedSequence p q) {l | l.headI = 1}ᶜ = q / (p + q) := by
  have h' : (p + q : ℝ≥0∞) ≠ 0 := mod_cast h.ne'
  have := condCount_compl
    {l : List ℤ | l.headI = 1}ᶜ (countedSequence_finite p q) (countedSequence_nonempty p q)
  rw [compl_compl, first_vote_pos _ _ h] at this
  rw [← ENNReal.sub_eq_of_add_eq _ this, ENNReal.eq_div_iff, ENNReal.mul_sub, mul_one,
    ENNReal.mul_div_cancel', ENNReal.add_sub_cancel_left]
  all_goals simp_all [ENNReal.div_eq_top]
#align ballot.first_vote_neg Ballot.first_vote_neg

theorem ballot_same (p : ℕ) : condCount (countedSequence (p + 1) (p + 1)) staysPositive = 0 := by
  rw [condCount_eq_zero_iff (countedSequence_finite _ _), eq_empty_iff_forall_not_mem]
  rintro x ⟨hx, t⟩
  apply ne_of_gt (t x _ x.suffix_refl)
  · simpa using sum_of_mem_countedSequence hx
  · refine List.ne_nil_of_length_pos ?_
    rw [length_of_mem_countedSequence hx]
    exact Nat.add_pos_left (Nat.succ_pos _) _
#align ballot.ballot_same Ballot.ballot_same

theorem ballot_edge (p : ℕ) : condCount (countedSequence (p + 1) 0) staysPositive = 1 := by
  rw [counted_right_zero]
  refine condCount_eq_one_of (finite_singleton _) (singleton_nonempty _) ?_
  refine singleton_subset_iff.2 fun l hl₁ hl₂ => List.sum_pos _ (fun x hx => ?_) hl₁
  rw [List.eq_of_mem_replicate (List.mem_of_mem_suffix hx hl₂)]
  norm_num
#align ballot.ballot_edge Ballot.ballot_edge

theorem countedSequence_int_pos_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1} =
      (countedSequence p (q + 1)).image (List.cons 1) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons (-1) '' countedSequence (p + 1) q ∩ {l | l.headI = 1} = ∅), union_empty] <;>
    · ext
      simp only [mem_inter_iff, mem_image, mem_setOf_eq, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false_iff, not_and, forall_exists_index, and_imp]
      rintro y _ rfl
      norm_num
#align ballot.counted_sequence_int_pos_counted_succ_succ Ballot.countedSequence_int_pos_counted_succ_succ

theorem ballot_pos (p q : ℕ) :
    condCount (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}) staysPositive =
      condCount (countedSequence p (q + 1)) staysPositive := by
  rw [countedSequence_int_pos_counted_succ_succ, condCount, condCount,
    cond_apply _ list_int_measurableSet, cond_apply _ list_int_measurableSet,
    count_injective_image List.cons_injective]
  congr 1
  have : (1 :: ·) '' countedSequence p (q + 1) ∩ staysPositive =
      (1 :: ·) '' (countedSequence p (q + 1) ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons_pos _ one_pos]
    exact fun _ _ ↦ trivial
  rw [this, count_injective_image]
  exact List.cons_injective
#align ballot.ballot_pos Ballot.ballot_pos

theorem countedSequence_int_neg_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ =
      (countedSequence (p + 1) q).image (List.cons (-1)) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons 1 '' countedSequence p (q + 1) ∩ {l : List ℤ | l.headI = 1}ᶜ = ∅),
      empty_union] <;>
    · ext
      simp only [mem_inter_iff, mem_image, mem_setOf_eq, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false_iff, not_and, forall_exists_index, and_imp]
      rintro y _ rfl
      norm_num
#align ballot.counted_sequence_int_neg_counted_succ_succ Ballot.countedSequence_int_neg_counted_succ_succ

theorem ballot_neg (p q : ℕ) (qp : q < p) :
    condCount (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ) staysPositive =
      condCount (countedSequence (p + 1) q) staysPositive := by
  rw [countedSequence_int_neg_counted_succ_succ, condCount, condCount,
    cond_apply _ list_int_measurableSet, cond_apply _ list_int_measurableSet,
    count_injective_image List.cons_injective]
  congr 1
  have : List.cons (-1) '' countedSequence (p + 1) q ∩ staysPositive =
      List.cons (-1) '' (countedSequence (p + 1) q ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons, and_iff_left_iff_imp]
    intro l hl _
    simp [sum_of_mem_countedSequence hl, lt_sub_iff_add_lt', qp]
  rw [this, count_injective_image]
  exact List.cons_injective
#align ballot.ballot_neg Ballot.ballot_neg

theorem ballot_problem' :
    ∀ q p, q < p → (condCount (countedSequence p q) staysPositive).toReal = (p - q) / (p + q) := by
  classical
  apply Nat.diag_induction
  · intro p
    rw [ballot_same]
    simp
  · intro p
    rw [ballot_edge]
    simp only [ENNReal.one_toReal, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, add_zero]
    rw [div_self]
    exact Nat.cast_add_one_ne_zero p
  · intro q p qp h₁ h₂
    haveI := condCount_isProbabilityMeasure
      (countedSequence_finite p (q + 1)) (countedSequence_nonempty _ _)
    haveI := condCount_isProbabilityMeasure
      (countedSequence_finite (p + 1) q) (countedSequence_nonempty _ _)
    have h₃ : p + 1 + (q + 1) > 0 := Nat.add_pos_left (Nat.succ_pos _) _
    rw [← condCount_add_compl_eq {l : List ℤ | l.headI = 1} _ (countedSequence_finite _ _),
      first_vote_pos _ _ h₃, first_vote_neg _ _ h₃, ballot_pos, ballot_neg _ _ qp]
    rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul, ← Nat.cast_add,
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_nat, ENNReal.toReal_nat,
      ENNReal.toReal_nat, h₁, h₂]
    · have h₄ : (p + 1 : ℝ) + (q + 1 : ℝ) ≠ (0 : ℝ) := by
        apply ne_of_gt
        assumption_mod_cast
      have h₅ : (p + 1 : ℝ) + ↑q ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      have h₆ : ↑p + (q + 1 : ℝ) ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      field_simp [h₄, h₅, h₆] at *
      ring
    all_goals
      refine (ENNReal.mul_lt_top ?_ ?_).ne
      · exact (measure_lt_top _ _).ne
      · simp [Ne, ENNReal.div_eq_top]
#align ballot.ballot_problem' Ballot.ballot_problem'

/-- The ballot problem. -/
theorem ballot_problem :
    ∀ q p, q < p → condCount (countedSequence p q) staysPositive = (p - q) / (p + q) := by
  intro q p qp
  haveI :=
    condCount_isProbabilityMeasure (countedSequence_finite p q) (countedSequence_nonempty _ _)
  have :
    (condCount (countedSequence p q) staysPositive).toReal =
      ((p - q) / (p + q) : ℝ≥0∞).toReal := by
    rw [ballot_problem' q p qp]
    rw [ENNReal.toReal_div, ← Nat.cast_add, ← Nat.cast_add, ENNReal.toReal_nat,
      ENNReal.toReal_sub_of_le, ENNReal.toReal_nat, ENNReal.toReal_nat]
    exacts [Nat.cast_le.2 qp.le, ENNReal.natCast_ne_top _]
  rwa [ENNReal.toReal_eq_toReal (measure_lt_top _ _).ne] at this
  simp only [Ne, ENNReal.div_eq_top, tsub_eq_zero_iff_le, Nat.cast_le, not_le,
    add_eq_zero_iff, Nat.cast_eq_zero, ENNReal.add_eq_top, ENNReal.natCast_ne_top, or_self_iff,
    not_false_iff, and_true_iff]
  push_neg
  exact ⟨fun _ _ => by linarith, (tsub_le_self.trans_lt (ENNReal.natCast_ne_top p).lt_top).ne⟩
#align ballot.ballot_problem Ballot.ballot_problem

end Ballot
