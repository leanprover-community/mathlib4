/-
Copyright (c) 2022 Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kexing Ying

! This file was ported from Lean 3 source module wiedijk_100_theorems.ballot_problem
! leanprover-community/mathlib commit 5563b1b49e86e135e8c7b556da5ad2f5ff881cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Probability.CondCount

/-!
# Ballot problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The ballot problem asks, if in an election, candidate A receives `p` votes whereas candidate B
receives `q` votes where `p > q`, what is the probability that candidate A is strictly ahead
throughout the count. The probability of this is `(p - q) / (p + q)`.

## Main definitions

* `counted_sequence`: given natural numbers `p` and `q`, `counted_sequence p q` is the set of
  all lists containing `p` of `1`s and `q` of `-1`s representing the votes of candidate A and B
  respectively.
* `stays_positive`: is the set of lists of integers which suffix has positive sum. In particular,
  the intersection of this set with `counted_sequence` is the set of lists where candidate A is
  strictly ahead.

## Main result

* `ballot`: the ballot problem.

-/


open Set ProbabilityTheory MeasureTheory

namespace Ballot

/-- The set of nonempty lists of integers which suffix has positive sum. -/
def staysPositive : Set (List ℤ) :=
  {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.Sum}
#align ballot.stays_positive Ballot.staysPositive

@[simp]
theorem staysPositive_nil : [] ∈ staysPositive := fun l hl hl₁ =>
  (hl (List.eq_nil_of_suffix_nil hl₁)).elim
#align ballot.stays_positive_nil Ballot.staysPositive_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem staysPositive_cons_pos (x : ℤ) (hx : 0 < x) (l : List ℤ) :
    (x::l) ∈ staysPositive ↔ l ∈ staysPositive := by
  constructor
  · intro hl l₁ hl₁ hl₂
    apply hl l₁ hl₁ (hl₂.trans (List.suffix_cons _ _))
  · intro hl l₁ hl₁ hl₂
    rw [List.suffix_cons_iff] at hl₂ 
    rcases hl₂ with (rfl | hl₂)
    · rw [List.sum_cons]
      apply add_pos_of_pos_of_nonneg hx
      cases' l with hd tl
      · simp
      · apply le_of_lt (hl (hd::tl) (List.cons_ne_nil hd tl) (hd::tl).suffix_refl)
    · apply hl _ hl₁ hl₂
#align ballot.stays_positive_cons_pos Ballot.staysPositive_cons_pos

/-- `counted_sequence p q` is the set of lists of integers for which every element is `+1` or `-1`,
there are `p` lots of `+1` and `q` lots of `-1`.

This represents vote sequences where candidate `+1` receives `p` votes and candidate `-1` receives
`q` votes.
-/
def countedSequence (p q : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}
#align ballot.counted_sequence Ballot.countedSequence

/-- An alternative definition of `counted_sequence` that uses `list.perm`. -/
theorem mem_countedSequence_iff_perm {p q l} :
    l ∈ countedSequence p q ↔ l ~ List.replicate p (1 : ℤ) ++ List.replicate q (-1) := by
  rw [List.perm_replicate_append_replicate]
  · simp only [counted_sequence, List.subset_def, mem_set_of_eq, List.mem_cons, List.mem_singleton]
  · norm_num1
#align ballot.mem_counted_sequence_iff_perm Ballot.mem_countedSequence_iff_perm

@[simp]
theorem counted_right_zero (p : ℕ) : countedSequence p 0 = {List.replicate p 1} := by ext l;
  simp [mem_counted_sequence_iff_perm]
#align ballot.counted_right_zero Ballot.counted_right_zero

@[simp]
theorem counted_left_zero (q : ℕ) : countedSequence 0 q = {List.replicate q (-1)} := by ext l;
  simp [mem_counted_sequence_iff_perm]
#align ballot.counted_left_zero Ballot.counted_left_zero

theorem mem_of_mem_countedSequence {p q} {l} (hl : l ∈ countedSequence p q) {x : ℤ} (hx : x ∈ l) :
    x = 1 ∨ x = -1 :=
  hl.2.2 x hx
#align ballot.mem_of_mem_counted_sequence Ballot.mem_of_mem_countedSequence

theorem length_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.length = p + q := by simp [(mem_counted_sequence_iff_perm.1 hl).length_eq]
#align ballot.length_of_mem_counted_sequence Ballot.length_of_mem_countedSequence

theorem counted_eq_nil_iff {p q : ℕ} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l = [] ↔ p = 0 ∧ q = 0 :=
  List.length_eq_zero.symm.trans <| by simp [length_of_mem_counted_sequence hl]
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
  rw [counted_sequence, counted_sequence, counted_sequence]
  constructor
  · intro hl
    have hlnil := counted_ne_nil_left (Nat.succ_ne_zero p) hl
    obtain ⟨hl₀, hl₁, hl₂⟩ := hl
    obtain hlast | hlast := hl₂ l.head (List.head!_mem_self hlnil)
    · refine' Or.inl ⟨l.tail, ⟨_, _, _⟩, _⟩
      · rw [List.count_tail l 1 (List.length_pos_of_ne_nil hlnil), hl₀, if_pos,
          Nat.add_succ_sub_one, add_zero]
        rw [List.nthLe_zero, hlast]
      · rw [List.count_tail l (-1) (List.length_pos_of_ne_nil hlnil), hl₁, if_neg, Nat.sub_zero]
        rw [List.nthLe_zero, hlast]
        norm_num
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.cons_head!_tail hlnil]
    · refine' Or.inr ⟨l.tail, ⟨_, _, _⟩, _⟩
      · rw [List.count_tail l 1 (List.length_pos_of_ne_nil hlnil), hl₀, if_neg, Nat.sub_zero]
        rw [List.nthLe_zero, hlast]
        norm_num
      · rw [List.count_tail l (-1) (List.length_pos_of_ne_nil hlnil), hl₁, if_pos,
          Nat.add_succ_sub_one, add_zero]
        rw [List.nthLe_zero, hlast]
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.cons_head!_tail hlnil]
  · rintro (⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩ | ⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩)
    · refine' ⟨_, _, _⟩
      · rw [List.count_cons, if_pos rfl, ht₀]
      · rw [List.count_cons, if_neg, ht₁]
        norm_num
      · rintro x (hx | hx)
        exacts [Or.inl hx, ht₂ x hx]
    · refine' ⟨_, _, _⟩
      · rw [List.count_cons, if_neg, ht₀]
        norm_num
      · rw [List.count_cons, if_pos rfl, ht₁]
      · rintro x (hx | hx)
        exacts [Or.inr hx, ht₂ x hx]
#align ballot.counted_succ_succ Ballot.counted_succ_succ

theorem countedSequence_finite : ∀ p q : ℕ, (countedSequence p q).Finite
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, Set.finite_union, Set.finite_image_iff (list.cons_injective.inj_on _),
      Set.finite_image_iff (list.cons_injective.inj_on _)]
    exact ⟨counted_sequence_finite _ _, counted_sequence_finite _ _⟩
#align ballot.counted_sequence_finite Ballot.countedSequence_finite

theorem countedSequence_nonempty : ∀ p q : ℕ, (countedSequence p q).Nonempty
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, union_nonempty, nonempty_image_iff]
    exact Or.inl (counted_sequence_nonempty _ _)
#align ballot.counted_sequence_nonempty Ballot.countedSequence_nonempty

theorem sum_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.Sum = p - q := by simp [(mem_counted_sequence_iff_perm.1 hl).sum_eq, sub_eq_add_neg]
#align ballot.sum_of_mem_counted_sequence Ballot.sum_of_mem_countedSequence

theorem disjoint_bits (p q : ℕ) :
    Disjoint (List.cons 1 '' countedSequence p (q + 1))
      (List.cons (-1) '' countedSequence (p + 1) q) := by
  simp_rw [disjoint_left, mem_image, not_exists, exists_imp]
  rintro _ _ ⟨_, rfl⟩ _ ⟨_, _, _⟩
#align ballot.disjoint_bits Ballot.disjoint_bits

open MeasureTheory.Measure

private def measureable_space_list_int : MeasurableSpace (List ℤ) :=
  ⊤

attribute [local instance] measureable_space_list_int

private theorem measurable_singleton_class_list_int : MeasurableSingletonClass (List ℤ) :=
  { measurableSet_singleton := fun s => trivial }

attribute [local instance] measurable_singleton_class_list_int

private theorem list_int_measurable_set {s : Set (List ℤ)} : MeasurableSet s :=
  trivial

theorem count_countedSequence : ∀ p q : ℕ, count (countedSequence p q) = (p + q).choose p
  | p, 0 => by simp [counted_right_zero, count_singleton]
  | 0, q => by simp [counted_left_zero, count_singleton]
  | p + 1, q + 1 => by
    rw [counted_succ_succ, measure_union (disjoint_bits _ _) list_int_measurable_set,
      count_injective_image List.cons_injective, count_counted_sequence,
      count_injective_image List.cons_injective, count_counted_sequence]
    · norm_cast
      rw [add_assoc, add_comm 1 q, ← Nat.choose_succ_succ, Nat.succ_eq_add_one, add_right_comm]
    all_goals try infer_instance
#align ballot.count_counted_sequence Ballot.count_countedSequence

theorem first_vote_pos :
    ∀ p q,
      0 < p + q → condCount (countedSequence p q : Set (List ℤ)) {l | l.headI = 1} = p / (p + q)
  | p + 1, 0, h => by
    rw [counted_right_zero, cond_count_singleton]
    simp [ENNReal.div_self _ _]
  | 0, q + 1, _ => by
    rw [counted_left_zero, cond_count_singleton]
    simpa
  | p + 1, q + 1, h => by
    simp_rw [counted_succ_succ]
    rw [←
      cond_count_disjoint_union ((counted_sequence_finite _ _).image _)
        ((counted_sequence_finite _ _).image _) (disjoint_bits _ _),
      ← counted_succ_succ,
      cond_count_eq_one_of ((counted_sequence_finite p (q + 1)).image _)
        (nonempty_image_iff.2 (counted_sequence_nonempty _ _))]
    · have : List.cons (-1) '' counted_sequence (p + 1) q ∩ {l : List ℤ | l.headI = 1} = ∅ := by
        ext
        simp only [mem_inter_iff, mem_image, mem_set_of_eq, mem_empty_iff_false, iff_false_iff,
          not_and, forall_exists_index, and_imp]
        rintro l _ rfl
        norm_num
      have hint :
        counted_sequence (p + 1) (q + 1) ∩ List.cons 1 '' counted_sequence p (q + 1) =
          List.cons 1 '' counted_sequence p (q + 1) := by
        rw [inter_eq_right_iff_subset, counted_succ_succ]
        exact subset_union_left _ _
      rw [(cond_count_eq_zero_iff <| (counted_sequence_finite _ _).image _).2 this, cond_count,
        cond_apply _ list_int_measurable_set, hint, count_injective_image List.cons_injective,
        count_counted_sequence, count_counted_sequence, one_mul, MulZeroClass.zero_mul, add_zero,
        Nat.cast_add, Nat.cast_one]
      · rw [mul_comm, ← div_eq_mul_inv, ENNReal.div_eq_div_iff]
        · norm_cast
          rw [mul_comm _ (p + 1), ← Nat.succ_eq_add_one p, Nat.succ_add, Nat.succ_mul_choose_eq,
            mul_comm]
        all_goals simp [(Nat.choose_pos <| (le_add_iff_nonneg_right _).2 zero_le').Ne.symm]
      all_goals infer_instance
    · simp
    · infer_instance
#align ballot.first_vote_pos Ballot.first_vote_pos

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem headI_mem_of_nonempty {α : Type _} [Inhabited α] : ∀ {l : List α} (hl : l ≠ []), l.headI ∈ l
  | [], h => h rfl
  | x::l, _ => Or.inl rfl
#align ballot.head_mem_of_nonempty Ballot.headI_mem_of_nonempty

theorem first_vote_neg (p q : ℕ) (h : 0 < p + q) :
    condCount (countedSequence p q) ({l | l.headI = 1}ᶜ) = q / (p + q) := by
  have :=
    cond_count_compl ({l : List ℤ | l.headI = 1}ᶜ) (counted_sequence_finite p q)
      (counted_sequence_nonempty p q)
  rw [compl_compl, first_vote_pos _ _ h] at this 
  rw [(_ : (q / (p + q) : ENNReal) = 1 - p / (p + q)), ← this, ENNReal.add_sub_cancel_right]
  · simp only [Ne.def, ENNReal.div_eq_top, Nat.cast_eq_zero, add_eq_zero_iff, ENNReal.nat_ne_top,
      false_and_iff, or_false_iff, not_and]
    intros
    contradiction
  rw [eq_comm, ENNReal.eq_div_iff, ENNReal.mul_sub, ENNReal.mul_div_cancel']
  all_goals simp; try rintro rfl; rw [zero_add] at h ; exact h.ne.symm
#align ballot.first_vote_neg Ballot.first_vote_neg

theorem ballot_same (p : ℕ) : condCount (countedSequence (p + 1) (p + 1)) staysPositive = 0 := by
  rw [cond_count_eq_zero_iff (counted_sequence_finite _ _), eq_empty_iff_forall_not_mem]
  rintro x ⟨hx, t⟩
  apply ne_of_gt (t x _ x.suffix_refl)
  · simpa using sum_of_mem_counted_sequence hx
  · refine' List.ne_nil_of_length_pos _
    rw [length_of_mem_counted_sequence hx]
    exact Nat.add_pos_left (Nat.succ_pos _) _
#align ballot.ballot_same Ballot.ballot_same

theorem ballot_edge (p : ℕ) : condCount (countedSequence (p + 1) 0) staysPositive = 1 := by
  rw [counted_right_zero]
  refine' cond_count_eq_one_of (finite_singleton _) (singleton_nonempty _) _
  · intro l hl
    rw [mem_singleton_iff] at hl 
    subst hl
    refine' fun l hl₁ hl₂ => List.sum_pos _ (fun x hx => _) hl₁
    rw [List.eq_of_mem_replicate (List.mem_of_mem_suffix hx hl₂)]
    norm_num
#align ballot.ballot_edge Ballot.ballot_edge

theorem countedSequence_int_pos_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1} =
      (countedSequence p (q + 1)).image (List.cons 1) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons (-1) '' counted_sequence (p + 1) q ∩ {l | l.headI = 1} = ∅), union_empty] <;>
    · ext
      simp only [mem_inter_iff, mem_image, mem_set_of_eq, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false_iff, not_and, forall_exists_index, and_imp]
      rintro y hy rfl
      norm_num
#align ballot.counted_sequence_int_pos_counted_succ_succ Ballot.countedSequence_int_pos_counted_succ_succ

theorem ballot_pos (p q : ℕ) :
    condCount (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}) staysPositive =
      condCount (countedSequence p (q + 1)) staysPositive := by
  rw [counted_sequence_int_pos_counted_succ_succ, cond_count, cond_count,
    cond_apply _ list_int_measurable_set, cond_apply _ list_int_measurable_set,
    count_injective_image List.cons_injective]
  all_goals try infer_instance
  congr 1
  have :
    (counted_sequence p (q + 1)).image (List.cons 1) ∩ stays_positive =
      (counted_sequence p (q + 1) ∩ stays_positive).image (List.cons 1) := by
    ext t
    simp only [mem_inter_iff, mem_image]
    constructor
    · simp only [and_imp, exists_imp]
      rintro l hl rfl t
      refine' ⟨l, ⟨hl, _⟩, rfl⟩
      rwa [stays_positive_cons_pos] at t 
      norm_num
    · simp only [and_imp, exists_imp]
      rintro l hl₁ hl₂ rfl
      refine' ⟨⟨_, hl₁, rfl⟩, _⟩
      rwa [stays_positive_cons_pos]
      norm_num
  rw [this, count_injective_image]
  exact List.cons_injective
#align ballot.ballot_pos Ballot.ballot_pos

theorem countedSequence_int_neg_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ =
      (countedSequence (p + 1) q).image (List.cons (-1)) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons 1 '' counted_sequence p (q + 1) ∩ {l : List ℤ | l.headI = 1}ᶜ = ∅),
      empty_union] <;>
    · ext
      simp only [mem_inter_iff, mem_image, mem_set_of_eq, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false_iff, not_and, forall_exists_index, and_imp]
      rintro y hy rfl
      norm_num
#align ballot.counted_sequence_int_neg_counted_succ_succ Ballot.countedSequence_int_neg_counted_succ_succ

theorem ballot_neg (p q : ℕ) (qp : q < p) :
    condCount (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ) staysPositive =
      condCount (countedSequence (p + 1) q) staysPositive := by
  rw [counted_sequence_int_neg_counted_succ_succ, cond_count, cond_count,
    cond_apply _ list_int_measurable_set, cond_apply _ list_int_measurable_set,
    count_injective_image List.cons_injective]
  all_goals try infer_instance
  congr 1
  have :
    (counted_sequence (p + 1) q).image (List.cons (-1)) ∩ stays_positive =
      (counted_sequence (p + 1) q ∩ stays_positive).image (List.cons (-1)) := by
    ext t
    simp only [mem_inter_iff, mem_image]
    constructor
    · simp only [and_imp, exists_imp]
      rintro l hl rfl t
      exact ⟨_, ⟨hl, fun l₁ hl₁ hl₂ => t l₁ hl₁ (hl₂.trans (List.suffix_cons _ _))⟩, rfl⟩
    · simp only [and_imp, exists_imp]
      rintro l hl₁ hl₂ rfl
      refine' ⟨⟨l, hl₁, rfl⟩, fun l₁ hl₃ hl₄ => _⟩
      rw [List.suffix_cons_iff] at hl₄ 
      rcases hl₄ with (rfl | hl₄)
      · simp [List.sum_cons, sum_of_mem_counted_sequence hl₁, sub_eq_add_neg, ← add_assoc, qp]
      exact hl₂ _ hl₃ hl₄
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
    haveI :=
      cond_count_is_probability_measure (counted_sequence_finite p (q + 1))
        (counted_sequence_nonempty _ _)
    haveI :=
      cond_count_is_probability_measure (counted_sequence_finite (p + 1) q)
        (counted_sequence_nonempty _ _)
    have h₃ : p + 1 + (q + 1) > 0 := Nat.add_pos_left (Nat.succ_pos _) _
    rw [← cond_count_add_compl_eq {l : List ℤ | l.headI = 1} _ (counted_sequence_finite _ _),
      first_vote_pos _ _ h₃, first_vote_neg _ _ h₃, ballot_pos, ballot_neg _ _ qp]
    rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_mul, ← Nat.cast_add,
      ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_nat, ENNReal.toReal_nat,
      ENNReal.toReal_nat, h₁, h₂]
    · have h₄ : ↑(p + 1) + ↑(q + 1) ≠ (0 : ℝ) := by
        apply ne_of_gt
        assumption_mod_cast
      have h₅ : ↑(p + 1) + ↑q ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      have h₆ : ↑p + ↑(q + 1) ≠ (0 : ℝ) := by
        apply ne_of_gt
        norm_cast
        linarith
      field_simp [h₄, h₅, h₆] at *
      ring
    all_goals
      refine' (ENNReal.mul_lt_top (measure_lt_top _ _).Ne _).Ne
      simp [Ne.def, ENNReal.div_eq_top]
#align ballot.ballot_problem' Ballot.ballot_problem'

/-- The ballot problem. -/
theorem ballot_problem :
    ∀ q p, q < p → condCount (countedSequence p q) staysPositive = (p - q) / (p + q) := by
  intro q p qp
  haveI :=
    cond_count_is_probability_measure (counted_sequence_finite p q) (counted_sequence_nonempty _ _)
  have :
    (cond_count (counted_sequence p q) stays_positive).toReal =
      ((p - q) / (p + q) : ENNReal).toReal := by
    rw [ballot_problem' q p qp]
    rw [ENNReal.toReal_div, ← Nat.cast_add, ← Nat.cast_add, ENNReal.toReal_nat,
      ENNReal.toReal_sub_of_le, ENNReal.toReal_nat, ENNReal.toReal_nat]
    exacts [Nat.cast_le.2 qp.le, ENNReal.nat_ne_top _]
  rwa [ENNReal.toReal_eq_toReal (measure_lt_top _ _).Ne] at this 
  · simp only [Ne.def, ENNReal.div_eq_top, tsub_eq_zero_iff_le, Nat.cast_le, not_le,
      add_eq_zero_iff, Nat.cast_eq_zero, ENNReal.add_eq_top, ENNReal.nat_ne_top, or_self_iff,
      not_false_iff, and_true_iff]
    push_neg
    exact ⟨fun _ _ => by linarith, (lt_of_le_of_lt tsub_le_self (ENNReal.nat_ne_top p).lt_top).Ne⟩
  infer_instance
#align ballot.ballot_problem Ballot.ballot_problem

end Ballot

