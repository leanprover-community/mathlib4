/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Hensel
import Mathlib.Data.DigitExpansion.Real.Basic

/-!
# Defining reals without the use of rationals, the subgroup of rationals and integers

* [Defining reals without the use of rationals][debruijn1976]

-/

variable (Z : Type*) [Nonempty Z] [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
  [NoMinOrder Z] [IsSuccArchimedean Z] (b : ℕ) [hb : NeZero b]
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

open Order

namespace DigitExpansion

/-- A sequence that is both real and Hensel is like the rationals. TODO: prove the equivalence.
These sequences form an additive subgroup. -/
def realHensel : AddSubgroup (DigitExpansion Z b) :=
  real Z b ⊓ hensel Z b

/-- A sequence that is both real and Hensel as an additive subgroup of the real sequences. -/
def real.hensel : AddSubgroup (real Z b) :=
  (realHensel Z b).comap (AddSubgroup.subtype _)

/-- A sequence that is both real and a Hensel integer. TODO: prove the equivalence to integers.
These sequences form an additive subgroup. -/
def zStar [Zero Z] : AddSubgroup (DigitExpansion Z b) :=
  real Z b ⊓ henselInt Z b

variable {Z} {b}

theorem real.dense {f g : real Z b} (hfg : f > g) :
    ∃ h ∈ real.hensel Z b, f > h ∧ h > g := by
  set k := f - g with hk
  have kpos : DigitExpansion.Positive (k : DigitExpansion Z b) := by
    rw [real.positive_iff, hk]
    exact sub_pos_of_lt hfg
  obtain ⟨x, xpos, hx⟩ := kpos.exists_least_pos
  let p' : DigitExpansion Z b := ⟨fun y => if y ≤ x then 0 else if y = succ x then 1
    else (f : DigitExpansion Z b) y, ?_⟩
  swap
  · rintro ⟨z, hz⟩
    obtain ⟨w, hwz, hw⟩ := exists_bounded (f : DigitExpansion Z b) z
    cases' le_or_lt w x with h h
    · specialize hz _ hwz
      simp only at hz
      rw [if_pos h, ← Fin.val_last b, Fin.cast_val_eq_self] at hz
      cases b
      · exact absurd rfl hb.out
      · exact (Fin.last_pos : 0 < Fin.last _).ne hz
    · obtain ⟨w', hww', hw'⟩ := exists_bounded (f : DigitExpansion Z b) (succ w)
      specialize hz w' ((lt_trans hwz (lt_succ _)).trans hww')
      simp only at hz
      rw [if_neg ((succ_strictMono h).trans hww').ne',
        if_neg (not_le_of_lt (h.trans ((lt_succ _).trans hww')))] at hz
      exact hw'.ne hz
  have px0 : ∀ y ≤ x, p' y = 0 := by
    intro y hy
    exact if_pos hy
  have ppos : p'.Positive := by
    refine' ⟨fun H => _, x, _⟩
    · replace H : p' (succ x) = 0
      · rw [H, zero_apply]
      simp [p', hb.out] at H
    · intro y hy
      exact px0 _ hy.le
  let p : real Z b := ⟨p', Or.inl ppos⟩
  refine' ⟨f - p, ⟨(f - p).prop, succ x, _⟩, _, _⟩
  · intro z hz
    simp only [DigitExpansion.sub_def, AddSubgroup.coeSubtype, AddSubgroup.coe_sub, Subtype.coe_mk,
      mk_apply, ne_of_gt hz, not_le_of_lt ((lt_trans (lt_succ x)) hz),
      difcar_eq_zero_iff, if_false, sub_self, zero_sub,
      neg_eq_zero, gt_iff_lt]
    intro w hzw
    simp [not_le_of_lt (lt_trans (lt_succ x) (lt_trans hz hzw)), ne_of_gt (lt_trans hz hzw)]
  · rw [gt_iff_lt, sub_lt_comm, sub_self, ← real.positive_iff]
    exact ppos
  suffices k > p by
    rwa [gt_iff_lt, ← add_lt_add_iff_left (g - p), hk, sub_add_sub_cancel', sub_add_cancel] at this
  rw [gt_iff_lt, real.lt_def]
  refine' ((kpos.sub_positive ppos fun H => xpos.ne _).resolve_right _).left
  · rw [H, px0 _ le_rfl]
  · push_neg
    refine' fun _ => ⟨x, _, fun y hy => _⟩
    · rwa [px0 _ le_rfl]
    · rw [hx _ hy, px0 _ hy.le]

theorem real.exists_lt_zStar [Zero Z] (f : real Z b) :
    ∃ h : zStar Z b, (⟨_, h.prop.left⟩ : real Z b) > f := by
  let q' : DigitExpansion Z b := ⟨fun x => if x ≤ 0 then b else (f : DigitExpansion Z b) x, ?_⟩
  swap
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx, hx'⟩ := exists_bounded (f : DigitExpansion Z b) (max (succ z) (succ 0))
    refine' hx'.ne _
    simp only at hz
    rw [← hz x (lt_trans _ hx), if_neg (not_le_of_lt (lt_trans _ hx))] <;>
      simp
  have qneg : q'.Negative := by
    refine' ⟨fun H => _, 0, fun y hy => _⟩
    · replace H : q' 0 = 0
      · rw [H, zero_apply]
      simp only [q', mk_apply, if_pos le_rfl] at H
      rw [← Fin.val_last b, Fin.cast_val_eq_self] at H
      cases b
      · exact absurd rfl hb.out
      · exact (Fin.last_pos : 0 < Fin.last _).ne' H
    · simp [q', hy.not_lt]
  let q : real Z b := ⟨q', Or.inr (Or.inl qneg)⟩
  refine' ⟨⟨f - q, (f - q).prop, fun z zpos => _⟩, _⟩
  · simp only [DigitExpansion.sub_def, not_le_of_lt zpos,
      difcar_eq_zero_iff, Subtype.coe_mk, mk_apply, if_false, sub_self, zero_sub,
      neg_eq_zero, gt_iff_lt]
    intro x hx
    simp [(hx.trans' zpos).not_le]
  · change f < f - q
    rwa [lt_sub_comm, sub_self, ← real.negative_iff]

namespace zStar

variable [Zero Z]

noncomputable
instance : LinearOrderedAddCommGroup (zStar Z b) :=
  { LinearOrder.lift' (fun ⟨x, hx⟩ ↦ ⟨x, hx.left⟩ : zStar Z b → real Z b) (by
      rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
      simp) with
    add_le_add_left := by
      rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩ h ⟨z, hz, hz'⟩
      have : (⟨x, hx⟩ : real Z b) ≤ ⟨y, hy⟩ := h
      exact add_le_add_left this ⟨z, hz⟩ }

protected lemma zStar.le_def {x y : zStar Z b} :
    x ≤ y ↔ (⟨x.val, x.prop.left⟩ : real Z b) ≤ ⟨y.val, y.prop.left⟩ := Iff.rfl

protected lemma zStar.lt_def {x y : zStar Z b} :
    x < y ↔ (⟨x.val, x.prop.left⟩ : real Z b) < ⟨y.val, y.prop.left⟩ := Iff.rfl

lemma positive_iff {x : zStar Z b} :
    DigitExpansion.Positive x.val ↔ 0 < x :=
  real.positive_iff (f := ⟨x.val, _⟩)

lemma negative_iff {x : zStar Z b} :
    DigitExpansion.Negative x.val ↔ x < 0 :=
  real.negative_iff (f := ⟨x.val, _⟩)

/-- An auxiliary function defining a sequence that has the specified digit at the specified
position, and 0 elsewhere. Compare to `Pi.single`. Not included in the de Bruijn paper. -/
def single {z : Z} (hz : z ≤ 0) (n : Fin (b + 1)) : zStar Z b :=
  ⟨(real.single z n).val, SetLike.coe_mem _, single_henselInt _ _ hz⟩

@[simp]
lemma val_single {z : Z} (hz : z ≤ 0) (n : Fin (b + 1)) :
    (single hz n).val = DigitExpansion.single z n := rfl

instance : One (zStar Z b) where
  one := single le_rfl 1

protected lemma one_def : (1 : zStar Z b) = single le_rfl 1 := rfl

protected lemma one_pos : (0 : zStar Z b) < 1 := by
  have h1 : ((1 : Fin (b + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt]
    simp [Nat.pos_of_ne_zero hb.out]
  have h01 : (1 : Fin (b + 1)) ≠ 0 := by
    rw [ne_comm, Fin.ne_iff_vne, h1]
    simp
  have := single_positive_of_ne_zero (0 : Z) h01
  rw [← positive_iff]
  exact this

@[simp]
lemma val_one_apply_zero : (1 : zStar Z b).val 0 = 1 := if_pos rfl

instance : ZeroLEOneClass (zStar Z b) where
  zero_le_one := zStar.one_pos.le

instance : NeZero (1 : zStar Z b) :=
  ⟨zStar.one_pos.ne'⟩

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

-- TODO: put in Hensel file
lemma exists_greatest_pos_of_ne_zero {a : zStar Z b} (h : a ≠ 0) :
    ∃ x ≤ 0, 0 < a.val x ∧ ∀ y > x, a.val y = 0 := by
  rw [ne_eq, Subtype.ext_iff, ← ne_eq, FunLike.ne_iff] at h
  obtain ⟨x, hx⟩ := h
  have xneg : x ≤ 0 := by
    contrapose! hx
    simp [a.prop.right _ hx]
  contrapose! xneg
  rw [← not_le]
  intro H
  obtain ⟨k, hk⟩ := exists_succ_iterate_of_le H
  replace this : ∀ m, a.val (succ^[m] x) ≠ 0 → ∃ y > (succ^[m] x), 0 < a.val y := by
    intro m hm
    have hn : succ^[m] x ≤ 0 := by
      contrapose! hm
      rw [a.prop.right _ hm]
    refine (xneg _ hn (Fin.pos_of_ne_zero hm)).imp ?_
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
  have hl := (f'^[k + 1] ⟨0, by simpa using hx⟩).prop
  rw [a.prop.right] at hl
  · exact absurd rfl hl
  · rw [← hk]
    exact succ_iterate_strict_mono key _

-- TODO
@[simp]
lemma Fin.lt_one_iff' {n : ℕ} [hn : NeZero n] (x : Fin (n + 1)) : x < 1 ↔ x = 0 := by
  cases' n
  · simp at hn
  simp [Fin.lt_iff_val_lt_val, Fin.ext_iff]

lemma one_le_iff_pos {x : zStar Z b} :
    1 ≤ x ↔ 0 < x := by
  constructor
  · intro h
    exact h.trans_lt' one_pos
  · intro h
    obtain ⟨z, zpos, hz'⟩ := (positive_iff.mpr h).exists_least_pos
    have hz : z ≤ 0 := by
      contrapose! zpos
      simp [x.prop.right _ zpos]
    rcases hz.eq_or_lt with rfl|hz
    · rw [zStar.le_def, real.le_def]
      rcases eq_or_ne (x.val 0) 1 with hx'|hx'
      · refine Or.inl ?_
        ext y
        rcases lt_trichotomy y 0 with hy|rfl|hy
        · simp [zStar.one_def, single_apply_of_ne _ _ _ hy.ne', hz' _ hy]
        · simp [zStar.one_def, hx']
        · simp [zStar.one_def, single_apply_of_ne _ _ _ hy.ne, x.prop.right _ hy]
      · refine Or.inr ⟨?_, 0, ?_⟩
        · rw [sub_ne_zero]
          simp only [SetLike.coe_eq_coe, FunLike.ne_iff]
          refine ⟨0, ?_⟩
          simp [zStar.one_def, hx']
        · intro y hy
          simp only [zStar.one_def, val_single, DigitExpansion.sub_def, hz' _ hy, ne_eq, hy.ne',
            not_false_eq_true, single_apply_of_ne, sub_self, zero_sub, neg_eq_zero,
            difcar_eq_zero_iff, gt_iff_lt]
          intro w
          rcases eq_or_ne w 0 with rfl|hw
          · simp [zpos.ne']
          · simp [single_apply_of_ne _ _ _ hw.symm]
    · refine Or.inr ⟨?_, z, ?_⟩
      · rw [sub_ne_zero]
        simp only [SetLike.coe_eq_coe, FunLike.ne_iff]
        refine ⟨z, ?_⟩
        simp [single_apply_of_ne _ _ _ hz.ne', zpos.ne']
      · intro y hy
        simp only [val_single, DigitExpansion.sub_def, hz' _ hy,
          single_apply_of_ne _ _ _ (hy.trans hz).ne', sub_self, zero_sub, neg_eq_zero,
          difcar_eq_zero_iff, gt_iff_lt]
        intro w
        rcases eq_or_ne w 0 with rfl|hw
        · intro _ _
          refine ⟨z, hz, hy, ?_⟩
          simp [single_apply_of_ne _ _ _ hz.ne', zpos]
        · simp [single_apply_of_ne _ _ _ hw.symm]

instance : NoMaxOrder (zStar Z b) where
  exists_gt := by
    rintro ⟨x, hx, hx'⟩
    by_cases posx : DigitExpansion.Positive x
    · refine ⟨⟨real.leftShift ⟨x, hx⟩, SetLike.coe_mem _, leftShift_henselInt hx'⟩, ?_⟩
      convert real.lt_leftShift_iff.mpr _
      rw [← real.positive_iff]
      exact posx
    · refine ⟨1, ?_⟩
      refine zStar.one_pos.trans_le' ?_
      contrapose! posx
      exact positive_iff.mpr posx

instance : NoMinOrder (zStar Z b) where
  exists_lt := by
    rintro ⟨x, hx, hx'⟩
    by_cases negx : DigitExpansion.Negative x
    · refine ⟨⟨real.leftShift ⟨x, hx⟩, SetLike.coe_mem _, leftShift_henselInt hx'⟩, ?_⟩
      convert real.leftShift_lt_iff.mpr _
      rw [← real.negative_iff]
      exact negx
    · refine ⟨-1, ?_⟩
      have : (-1 : zStar Z b) < 0 := by simp
      convert this.trans_le _
      contrapose! negx
      exact negative_iff.mpr negx

instance : SuccOrder (zStar Z b) where
  succ f := f + 1
  le_succ _ := by simp [one_pos.le]
  max_of_succ_le := by
    intro
    simp [one_pos]
  succ_le_of_lt := by
    intro x y h
    suffices 1 ≤ y - x by
      rwa [le_sub_iff_add_le'] at this
    simp [one_le_iff_pos, h]
  le_of_lt_succ := by
    intro x y h
    contrapose! h
    suffices 1 ≤ x - y by
      rwa [le_sub_iff_add_le'] at this
    simp [one_le_iff_pos, h]

instance : PredOrder (zStar Z b) where
  pred f := f - 1
  pred_le _ := by simp
  min_of_le_pred := by
    intro
    simp
  le_pred_of_lt := by
    intro _ _ h
    simp only [le_sub_iff_add_le, ge_iff_le]
    exact succ_le_of_lt h
  le_of_pred_lt := by
    intro _ _ h
    contrapose! h
    simp only [le_sub_iff_add_le, ge_iff_le]
    exact succ_le_of_lt h

end zStar

end DigitExpansion
