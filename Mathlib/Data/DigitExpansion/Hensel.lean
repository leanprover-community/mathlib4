/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Add
import Mathlib.GroupTheory.Subgroup.Basic

/-!
# Defining reals without the use of rationals, the Hensel subgroup

Constructing the actual subgroup of the k-adic numbers (no restriction on primality).

* [Defining reals without the use of rationals][debruijn1976]

-/

variable (Z : Type*) [Nonempty Z] [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
  [NoMinOrder Z] [IsSuccArchimedean Z] (b : ℕ) [hb : NeZero b]
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

open Order

-- TODO: IsSuccArchimedean docstring fix

-- TODO
lemma succ_iterate_strict_mono {α : Type*} [Preorder α] [SuccOrder α] [NoMaxOrder α] {m n : ℕ}
    (h : m < n) (x : α) : succ^[m] x < succ^[n] x := by
  induction' n with n IH generalizing m x
  · simp at h
  · simp only [Function.iterate_succ', Function.comp_apply]
    rcases (Nat.le_of_lt_succ h).eq_or_lt with rfl|h
    · exact lt_succ _
    exact (IH h _).trans (lt_succ _)

lemma succ_iterate_mono {α : Type*} [Preorder α] [SuccOrder α] [NoMaxOrder α] {m n : ℕ}
    (h : m ≤ n) (x : α) : succ^[m] x ≤ succ^[n] x := by
  rcases h.eq_or_lt with rfl|h
  · simp
  · exact (succ_iterate_strict_mono h _).le

namespace DigitExpansion

/-- A sequence is a Hensel (or b-adic) number if it has a right-tail of solely digit 0. These
sequences form an additive subgroup. -/
def hensel : AddSubgroup (DigitExpansion Z b) :=
  AddSubgroup.ofSub {f : DigitExpansion Z b | ∃ x, ∀ z > x, f z = 0} ⟨0, by simp⟩
    (by
      simp only [gt_iff_lt, Set.mem_setOf_eq, forall_exists_index]
      intro f x hfx g y hgy
      use max x y
      intro z hz
      simp only [max_lt_iff] at hz
      rw [← sub_eq_add_neg, DigitExpansion.sub_def, hfx _ hz.left, hgy _ hz.right]
      simp only [difcar_eq_zero_iff, sub_self, neg_zero, zero_sub, neg_eq_zero, gt_iff_lt]
      intro w hw
      simp [hfx _ (hz.left.trans hw), hgy _ (hz.right.trans hw)])

/-- A sequence is a Hensel (or b-adic) integer if the right-tail past the 0th digit is
solely digit 0. These sequences form an additive subgroup. -/
def henselInt [Zero Z] : AddSubgroup (DigitExpansion Z b) :=
  AddSubgroup.ofSub {f : DigitExpansion Z b | ∀ z > 0, f z = 0} ⟨0, by simp⟩
    (by
      simp only [gt_iff_lt, Set.mem_setOf_eq, forall_exists_index]
      intro f hf g hg z hz
      simp only [← sub_eq_add_neg, DigitExpansion.sub_def, hf _ hz, hg _ hz, difcar_eq_zero_iff,
        sub_self, neg_zero, zero_sub, neg_eq_zero, gt_iff_lt]
      intro w hw
      simp [hf _ (hw.trans' hz), hg _ (hw.trans' hz)])

variable {Z} {b}

lemma single_hensel (z : Z) (n : Fin (b + 1)) : single z n ∈ hensel Z b :=
  ⟨z, fun _ hx ↦ single_apply_of_ne _ _ _ hx.ne⟩

lemma single_henselInt [Zero Z] (z : Z) (n : Fin (b + 1)) (hz : z ≤ 0) :
    single z n ∈ henselInt Z b :=
  fun _ hx ↦ single_apply_of_ne _ _ _ (hx.trans_le' hz).ne

lemma shift_hensel {f : DigitExpansion Z b} (hf : f ∈ hensel Z b) :
    shift f ∈ hensel Z b := by
  obtain ⟨z, hz⟩ := hf
  refine' ⟨succ z, fun y hy ↦ ?_⟩
  have : z < pred y := by
    rwa [← succ_lt_succ_iff, succ_pred]
  simp [hz _ this]

lemma leftShift_hensel {f : DigitExpansion Z b} (hf : f ∈ hensel Z b) :
    leftShift f ∈ hensel Z b := by
  obtain ⟨z, hz⟩ := hf
  refine' ⟨succ z, fun y hy ↦ ?_⟩
  have : z < succ y := (le_succ _).trans_lt (hy.trans_le (le_succ _))
  simp [hz _ this]

lemma leftShift_henselInt [Zero Z] {f : DigitExpansion Z b} (hf : f ∈ henselInt Z b) :
    leftShift f ∈ henselInt Z b := by
  intro y hy
  have : 0 < succ y := (le_succ _).trans_lt' hy
  simp [hf _ this]

lemma zero_hensel : 0 ∈ hensel Z b := by
  inhabit Z
  exact ⟨default, by simp⟩

lemma zero_henselInt [Zero Z] : 0 ∈ henselInt Z b := fun _ _ ↦ by simp

lemma henselInt_le_hensel [Zero Z] : henselInt Z b ≤ hensel Z b :=
  fun _ hf ↦ ⟨0, hf⟩

lemma exists_greatest_pos_of_ne_zero {a : hensel Z b} (h : a ≠ 0) :
    ∃ x, 0 < a.val x ∧ ∀ y > x, a.val y = 0 := by
  rw [ne_eq, Subtype.ext_iff, ← ne_eq, FunLike.ne_iff] at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨l, hl⟩ := a.prop
  have xneg : x ≤ l := by
    contrapose! hx
    simp [hl _ hx]
  contrapose! xneg
  rw [← not_le]
  intro H
  obtain ⟨k, hk⟩ := exists_succ_iterate_of_le H
  replace this : ∀ m, a.val (succ^[m] x) ≠ 0 → ∃ y > (succ^[m] x), 0 < a.val y := by
    intro m hm
    refine (xneg _ (Fin.pos_of_ne_zero hm)).imp ?_
    intro y ⟨hy, hy'⟩
    exact ⟨hy, Fin.pos_of_ne_zero hy'⟩
  have hf' : ∀ l, a.val (succ^[l] x) ≠ 0 → ∃ l', l < l' ∧ a.val (succ^[l'] x) ≠ 0 := by
    intros l hl
    obtain ⟨y, hy, hy'⟩ := this l hl
    obtain ⟨l', rfl⟩ := exists_succ_iterate_of_le hy.le
    refine ⟨l' + l, ?_, ?_⟩
    · contrapose! hy
      simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hy
      simp [hy]
    · rw [Function.iterate_add, Function.comp_apply]
      exact hy'.ne'
  let f' : {l // a.val (succ^[l] x) ≠ 0} → {l // a.val (succ^[l] x) ≠ 0} := fun l ↦ ⟨
    Nat.find (hf' l.val l.prop),
    (Nat.find_spec (hf' l.val l.prop)).right
  ⟩
  have hf'' : ∀ l, l.val < (f' l).val := by
    rintro ⟨l, hl⟩
    have : (f' ⟨l, hl⟩).val = Nat.find (hf' l hl) := rfl
    rw [this]
    exact (Nat.find_spec (hf' l hl)).left
  have key : k < (f'^[k + 1] ⟨0, by simpa using hx⟩).val := by
    clear hk
    simp only [ne_eq, Function.iterate_succ, Function.comp_apply]
    induction' k with k IH
    · simp
    · rw [Function.iterate_succ', Function.comp_apply]
      refine (Nat.succ_le_succ IH).trans ?_
      rw [Nat.succ_le]
      exact hf'' _
  have hl' := (f'^[k + 1] ⟨0, by simpa using hx⟩).prop
  refine hl' (hl (succ^[_] x) ?_)
  rw [← hk]
  exact succ_iterate_strict_mono key _

namespace henselInt

variable [Zero Z]

/-- An auxiliary function defining a sequence that has the specified digit at the specified
position, and 0 elsewhere. Compare to `Pi.single`. Not included in the de Bruijn paper. -/
def single {z : Z} (hz : z ≤ 0) (n : Fin (b + 1)) : henselInt Z b :=
  ⟨DigitExpansion.single z n, single_henselInt _ _ hz⟩

@[simp]
lemma val_single {z : Z} (hz : z ≤ 0) (n : Fin (b + 1)) :
    (single hz n).val = DigitExpansion.single z n := rfl

instance : One (henselInt Z b) where
  one := single le_rfl 1

protected lemma one_def : (1 : henselInt Z b) = single le_rfl 1 := rfl

lemma fromHensel (f : hensel Z b) :
    ∃ (k : ℕ) (f' : henselInt Z b), shift^[k] f'.val = f := by
  rcases eq_or_ne f 0 with rfl|hf
  · exact ⟨0, 0, rfl⟩
  obtain ⟨x, -, hx⟩ := exists_greatest_pos_of_ne_zero hf
  rcases le_total x 0 with h0|h0
  · refine ⟨0, ⟨f.val, fun y hy ↦ hx _ (hy.trans_le' h0)⟩, rfl⟩
  revert hx f
  refine Succ.rec ?_ ?_ h0
  · intro f _ hx
    refine ⟨0, ⟨f.val, fun y hy ↦ hx _ hy⟩, rfl⟩
  intro x _ IH f hf IH'
  by_cases H : f.val (succ x) = 0
  · refine IH f hf (fun y hy ↦ ?_)
    rcases eq_or_ne y (succ x) with rfl|hy'
    · exact H
    · rw [IH']
      exact lt_of_le_of_ne (by simp [hy]) hy'.symm
  · specialize IH (⟨leftShift f.val, leftShift_hensel f.prop⟩) (by simp [hf]) _
    · intro y hy
      simp only [leftShift_apply]
      rw [IH']
      simp [hy]
    obtain ⟨k, f', hf'⟩ := IH
    refine ⟨k + 1, f', ?_⟩
    simp only [Function.iterate_succ', Function.comp_apply, hf']
    exact leftInverse_shift_leftShift _

end henselInt

end DigitExpansion
