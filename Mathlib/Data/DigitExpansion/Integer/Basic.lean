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

-- TODO
@[elab_as_elim]
def succArchimedeanRec {Z : Type*} [LinearOrder Z] [SuccOrder Z] [PredOrder Z]
    [IsSuccArchimedean Z] [NoMinOrder Z] [NoMaxOrder Z]
    {motive : Z → Sort*} {z : Z}
    (h0 : motive z)
    (hs : ∀ x, motive x → motive (succ x))
    (hp : ∀ x, motive x → motive (pred x)) (x : Z) : motive x :=
  if h : x ≤ z then by
    induction' hk : Nat.find (exists_succ_iterate_of_le h) with k IH generalizing x
    · simp only [Nat.zero_eq, Nat.find_eq_zero, Function.iterate_zero, id_eq] at hk
      exact hk ▸ h0
    · have hxz : succ x ≤ z := by
        rw [← Nat.find_spec (exists_succ_iterate_of_le h), hk, Function.iterate_succ',
            Function.comp_apply, succ_le_succ_iff]
        exact succ_iterate_mono (Nat.zero_le _) x
      have hk' : Nat.find (exists_succ_iterate_of_le hxz) = k := by
        rw [Nat.find_eq_iff] at hk ⊢
        rw [Function.iterate_succ, Function.comp_apply] at hk
        refine hk.imp_right ?_
        rintro hn' n hn rfl
        simpa using hn' (n + 1) (Nat.succ_lt_succ hn)
      exact pred_succ x ▸ hp _ (IH _ hxz hk')
  else by
    simp at h
    induction' hk : Nat.find (exists_succ_iterate_of_le (succ_le_of_lt h)) with k IH
      generalizing x
    · simp only [Nat.zero_eq, Nat.find_eq_zero, Function.iterate_zero, id_eq] at hk
      exact hk ▸ (hs _ h0)
    · simp only [Nat.find_eq_iff, Function.iterate_succ', Function.comp_apply] at hk
      have hxz : z < pred x := by
        rw [← hk.left, pred_succ]
        exact (lt_succ _).trans_le (succ_iterate_mono (Nat.zero_le _) (succ z))
      have hk' : Nat.find (exists_succ_iterate_of_le (succ_le_of_lt hxz)) = k := by
        rw [Nat.find_eq_iff, ← hk.left, pred_succ]
        rcases hk with ⟨rfl, hk⟩
        refine ⟨rfl, ?_⟩
        rintro n hn hn'
        specialize hk (n + 1) (Nat.succ_lt_succ hn)
        rw [Function.iterate_succ', Function.comp_apply, hn'] at hk
        exact hk rfl
      exact succ_pred x ▸ hs _ (IH _ hxz hk')

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

lemma zStar_le_realHensel [Zero Z] : zStar Z b ≤ realHensel Z b :=
  inf_le_inf_left _ (henselInt_le_hensel)

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

protected lemma le_def {x y : zStar Z b} :
    x ≤ y ↔ (⟨x.val, x.prop.left⟩ : real Z b) ≤ ⟨y.val, y.prop.left⟩ := Iff.rfl

protected lemma lt_def {x y : zStar Z b} :
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

lemma val_one_apply_ne {z : Z} (hz : z ≠ 0) : (1 : zStar Z b).val z = 0 := if_neg hz.symm

@[simp]
lemma neg_val_one_apply_zero : (-(1 : zStar Z b).val) 0 = b := by
  have : ((1 : zStar Z b) + -1).val 0 = 0 := by simp
  simp only [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid,
    DigitExpansion.add_def, DigitExpansion.sub_def] at this
  simp only [val_one_apply_zero, zero_apply, zero_sub, sub_neg_eq_add, zero_add, difcar_self,
  sub_zero] at this
  rw [sub_sub_eq_add_sub, sub_eq_zero, difcar_eq_zero_iff.mpr, add_zero] at this
  · nth_rewrite 1 [AddSubgroup.coe_neg] at this
    simp only [neg_neg, difcar_self, AddSubgroupClass.coe_neg, sub_neg_eq_add] at this
    rw [add_comm 1, add_eq_zero_iff_eq_neg] at this
    simp [this, neg_eq_iff_add_eq_zero, add_comm]
  · simp only [gt_iff_lt, zero_apply, Fin.not_lt_zero, and_false, exists_const, imp_false,
    not_lt, Fin.le_zero_iff]
    intro x hx
    exact (_ : zStar Z b).prop.right _ hx

lemma neg_val_one_apply_of_le {z : Z} (hz : z ≤ 0) : (-(1 : zStar Z b).val) z = b := by
  have : ((1 : zStar Z b) + -1).val z = 0 := by simp
  simp only [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid,
    DigitExpansion.add_def, DigitExpansion.sub_def] at this
  rcases hz.eq_or_lt with rfl|hz
  · simp
  · simp only [ne_eq, hz.ne, not_false_eq_true, val_one_apply_ne, zero_apply, zero_sub, neg_sub,
    AddSubgroupClass.coe_neg, sub_neg_eq_add, zero_add, difcar_self, sub_zero] at this
    rw [add_eq_zero_iff_neg_eq] at this
    rcases difcar_eq_zero_or_one 0 (-(1 : zStar Z b).val) z with hd|hd
    · rw [difcar_eq_zero_iff] at hd
      specialize hd 0 hz
      simp [Fin.ext_iff, hb.out] at hd
    rw [← this, hd]
    simp [neg_eq_iff_add_eq_zero, add_comm]

instance : ZeroLEOneClass (zStar Z b) where
  zero_le_one := zStar.one_pos.le

instance : NeZero (1 : zStar Z b) :=
  ⟨zStar.one_pos.ne'⟩

-- TODO: put in Hensel file
-- lemma exists_greatest_pos_of_ne_zero {a : zStar Z b} (h : a ≠ 0) :
--     ∃ x ≤ 0, 0 < a.val x ∧ ∀ y > x, a.val y = 0 := by
--   rw [ne_eq, Subtype.ext_iff, ← ne_eq, FunLike.ne_iff] at h
--   obtain ⟨x, hx⟩ := h
--   have xneg : x ≤ 0 := by
--     contrapose! hx
--     simp [a.prop.right _ hx]
--   contrapose! xneg
--   rw [← not_le]
--   intro H
--   obtain ⟨k, hk⟩ := exists_succ_iterate_of_le H
--   replace this : ∀ m, a.val (succ^[m] x) ≠ 0 → ∃ y > (succ^[m] x), 0 < a.val y := by
--     intro m hm
--     have hn : succ^[m] x ≤ 0 := by
--       contrapose! hm
--       rw [a.prop.right _ hm]
--     refine (xneg _ hn (Fin.pos_of_ne_zero hm)).imp ?_
--     intro y ⟨hy, hy'⟩
--     exact ⟨hy, Fin.pos_of_ne_zero hy'⟩
--   have hf' : ∀ l, a.val (succ^[l] x) ≠ 0 → ∃ l', l < l' ∧ a.val (succ^[l'] x) ≠ 0 := by
--     intros l hl
--     obtain ⟨y, hy, hy'⟩ := this l hl
--     obtain ⟨l', rfl⟩ := exists_succ_iterate_of_le hy.le
--     refine ⟨l' + l, ?_, ?_⟩
--     · contrapose! hy
--       simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hy
--       simp [hy]
--     · rw [Function.iterate_add, Function.comp_apply]
--       exact hy'.ne'
--   let f' : {l // a.val (succ^[l] x) ≠ 0} → {l // a.val (succ^[l] x) ≠ 0} := fun l ↦ ⟨
--     Nat.find (hf' l.val l.prop),
--     (Nat.find_spec (hf' l.val l.prop)).right
--   ⟩
--   have hf'' : ∀ l, l.val < (f' l).val := by
--     rintro ⟨l, hl⟩
--     have : (f' ⟨l, hl⟩).val = Nat.find (hf' l hl) := rfl
--     rw [this]
--     exact (Nat.find_spec (hf' l hl)).left
--   have key : k < (f'^[k + 1] ⟨0, by simpa using hx⟩).val := by
--     clear hk
--     simp only [ne_eq, Function.iterate_succ, Function.comp_apply]
--     induction' k with k IH
--     · simp
--     · rw [Function.iterate_succ', Function.comp_apply]
--       refine (Nat.succ_le_succ IH).trans ?_
--       rw [Nat.succ_le]
--       exact hf'' _
--   have hl := (f'^[k + 1] ⟨0, by simpa using hx⟩).prop
--   rw [a.prop.right] at hl
--   · exact absurd rfl hl
--   · rw [← hk]
--     exact succ_iterate_strict_mono key _

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
        · simp [val_one_apply_ne, hy.ne, hz' _ hy]
        · simp [hx']
        · simp [val_one_apply_ne, hy.ne', x.prop.right _ hy]
      · refine Or.inr ⟨?_, 0, ?_⟩
        · rw [sub_ne_zero]
          simp only [SetLike.coe_eq_coe, FunLike.ne_iff]
          refine ⟨0, ?_⟩
          simp [hx']
        · intro y hy
          simp only [val_one_apply_ne, hy.ne, DigitExpansion.sub_def, hz' _ hy, ne_eq, hy.ne',
            not_false_eq_true, single_apply_of_ne, sub_self, zero_sub, neg_eq_zero,
            difcar_eq_zero_iff, gt_iff_lt]
          intro w
          rcases eq_or_ne w 0 with rfl|hw
          · simp [zpos.ne']
          · simp [val_one_apply_ne, hw]
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

lemma single_eq_nsmul_one {x : Z} (k : ℕ) (hk : succ^[k] x = 0) (n : Fin (b + 1))
    (hx : x ≤ 0 := hk.le.trans' (succ_iterate_mono (Nat.zero_le k) x)) :
    single hx n = (((b + 1) ^ k) * n.val) • 1 := by
  induction' k with k IH generalizing x n
  · simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at hk
    simp [Subtype.ext_iff, zStar.one_def, nsmul_single_eq_single, hk]
  · specialize @IH (succ x) _ n _
    · simp [← hk, Function.iterate_succ']
    · simp only [← hk, Function.iterate_succ, Function.comp_apply, succ_le_iff]
      exact (lt_succ _).trans_le (succ_iterate_mono (Nat.zero_le k) _)
    rw [pow_succ, mul_assoc, mul_comm, mul_nsmul, ← IH]
    simp [Subtype.ext_iff, base_nsmul_single_succ_one_eq_single]

instance : IsSuccArchimedean (zStar Z b) where
  exists_succ_iterate_of_le := by
    intro x y h
    suffices ∃ k : ℕ, x + k • 1 = y by
      clear h
      obtain ⟨k, rfl⟩ := this
      induction' k with k IH generalizing x
      · refine ⟨0, ?_⟩
        simp
      · obtain ⟨k', hk'⟩ := @IH (x + 1)
        refine ⟨k' + 1, ?_⟩
        simpa [succ_nsmul, ← add_assoc] using hk'
    rcases h.eq_or_lt with rfl|h
    · exact ⟨0, by simp⟩
    replace h : 0 < y - x := by simp [h]
    rw [← positive_iff] at h
    obtain ⟨z, zpos, hz⟩ := h.exists_least_pos
    have negz : z ≤ 0 := by
      contrapose! zpos
      rw [(y - x).prop.right _ zpos]
    obtain ⟨k, hk⟩ := exists_succ_iterate_of_le negz
    clear h zpos negz
    clear h
    induction' k with k IH generalizing x y z
    · simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at hk
      subst hk
      refine ⟨(y - x).val 0, ?_⟩
      rw [eq_comm, ← sub_eq_iff_eq_add']
      convert single_eq_nsmul_one 0 rfl ((y - x).val 0) _
      · ext z : 2
        rcases lt_trichotomy 0 z with h|rfl|h
        · rw [(_ : zStar Z b).prop.right _ h, (_ : zStar Z b).prop.right _ h]
          simp
        · simp
        · rw [val_single, single_apply_of_ne _ _ _ h.ne', hz _ h]
      · simp
    · have hz' : z ≤ 0 := by
        rw [← hk]
        exact succ_iterate_mono (Nat.zero_le _) _
      suffices key : ∀ w < succ z, (y - x - single hz' ((y - x).val z)).val w = 0 by
        obtain ⟨l, hl⟩ := @IH (single hz' ((y - x).val z)) (y - x) (succ z) key hk
        rw [eq_comm, sub_eq_iff_eq_add, single_eq_nsmul_one (k + 1) hk, ← add_nsmul, add_comm] at hl
        exact ⟨_, hl.symm⟩
      intro w hw
      simp only [lt_succ_iff] at hw
      rcases hw.eq_or_lt with rfl|hw
      · simp only [AddSubgroupClass.coe_sub, DigitExpansion.sub_def, val_single, single_apply_self,
        sub_self, zero_sub, neg_eq_zero, difcar_eq_zero_iff, gt_iff_lt]
        intro u hu hu'
        rw [single_apply_of_ne _ _ _ hu.ne] at hu'
        exact absurd (Fin.zero_le _) hu'.not_le
      · rw [AddSubgroupClass.coe_sub, DigitExpansion.sub_def, hz _ hw, zero_sub]
        simp [single_apply_of_ne _ _ _ hw.ne']

lemma exists_nsmul_one_of_nonneg {f : zStar Z b} (hf : 0 ≤ f) : ∃ k : ℕ, f = k • 1 := by
  obtain ⟨k, rfl⟩ := exists_succ_iterate_of_le hf
  clear hf
  refine ⟨k, ?_⟩
  induction' k with k IH
  · simp
  · rw [Function.iterate_succ_apply', IH, succ_nsmul']
    rfl

end zStar

namespace realHensel

noncomputable
instance : LinearOrderedAddCommGroup (realHensel Z b) :=
  { LinearOrder.lift' (fun ⟨x, hx⟩ ↦ ⟨x, hx.left⟩ : realHensel Z b → real Z b) (by
      rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
      simp) with
    add_le_add_left := by
      rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩ h ⟨z, hz, hz'⟩
      have : (⟨x, hx⟩ : real Z b) ≤ ⟨y, hy⟩ := h
      exact add_le_add_left this ⟨z, hz⟩ }

protected lemma le_def {x y : realHensel Z b} :
    x ≤ y ↔ (⟨x.val, x.prop.left⟩ : real Z b) ≤ ⟨y.val, y.prop.left⟩ := Iff.rfl

protected lemma lt_def {x y : realHensel Z b} :
    x < y ↔ (⟨x.val, x.prop.left⟩ : real Z b) < ⟨y.val, y.prop.left⟩ := Iff.rfl

lemma positive_iff {x : realHensel Z b} :
    DigitExpansion.Positive x.val ↔ 0 < x :=
  real.positive_iff (f := ⟨x.val, _⟩)

lemma negative_iff {x : realHensel Z b} :
    DigitExpansion.Negative x.val ↔ x < 0 :=
  real.negative_iff (f := ⟨x.val, _⟩)

variable [Zero Z]

instance : One (realHensel Z b) where
  one := AddSubgroup.inclusion zStar_le_realHensel 1

protected lemma one_def : (1 : realHensel Z b) = AddSubgroup.inclusion zStar_le_realHensel 1 := rfl

/-- "Divide" the expansion by shifting the expansion one digit to the right. Also called
"half" in the orignal de Bruijn paper. -/
def shift (f : realHensel Z b) : realHensel Z b :=
  ⟨DigitExpansion.shift f.val, by simpa using (real.shift ⟨f.val, f.prop.left⟩).prop,
    shift_hensel f.prop.right⟩

@[simp]
lemma val_shift (f : realHensel Z b) : (shift f).val = f.val.shift := rfl

@[simp]
lemma val_iterate_shift (f : realHensel Z b) (k : ℕ) :
    (shift^[k] f).val = DigitExpansion.shift^[k] f.val := by
  induction k
  case zero => simp
  case succ k IH => simp only [Function.iterate_succ_apply', val_shift, IH]

end realHensel

lemma zStar.fromRealHensel [Zero Z] (f : realHensel Z b) :
    ∃ (k : ℕ) (f' : zStar Z b),
      realHensel.shift^[k] (AddSubgroup.inclusion zStar_le_realHensel f') = f := by
  obtain ⟨k, f', hf⟩ := henselInt.fromHensel ⟨f.val, f.prop.right⟩
  refine ⟨k, ⟨f'.val, ?_, f'.prop⟩, ?_⟩
  · simp only [AddSubgroup.coe_toAddSubmonoid, SetLike.mem_coe]
    suffices f'.val = leftShift^[k] f.val by
      rw [this]
      convert (real.leftShift^[k] ⟨f.val, f.prop.left⟩).prop
      clear this hf f'
      induction' k with k IH
      · simp
      · simp [- Function.iterate_succ, Function.iterate_succ', Function.comp_apply, IH]
    rw [← (leftInverse_shift_leftShift.iterate k).injective.eq_iff,
        (leftInverse_leftShift_shift.iterate k) _] at hf
    exact hf
  · rw [Subtype.ext_iff, realHensel.val_iterate_shift]
    exact hf

namespace realHensel

variable [Zero Z]

lemma inclusion_one : AddSubgroup.inclusion zStar_le_realHensel (1 : zStar Z b) = 1 := rfl

@[simp]
lemma base_nsmul_shift_eq (f : realHensel Z b) : (b + 1) • shift f = f := by
  obtain ⟨k, f', hk⟩ := zStar.fromRealHensel f
  ext : 1
  simp only [AddSubmonoidClass.coe_nsmul, val_shift, ← shift_nsmul_comm]
  rw [← hk]
  clear hk f
  simp only [val_iterate_shift, AddSubgroup.coe_inclusion]
  induction' k with k IH
  · simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
    rcases le_total 0 f' with fpos|fneg
    · obtain ⟨r, rfl⟩ := zStar.exists_nsmul_one_of_nonneg fpos
      simp only [map_nsmul, inclusion_one, AddSubmonoidClass.coe_nsmul,
        AddSubgroup.coe_toAddSubmonoid]
      rw [← mul_nsmul, mul_nsmul', zStar.one_def,
          zStar.val_single, ← succ_pred (0 : Z), base_nsmul_single_succ_one_eq_single,
          shift_nsmul_comm, shift_single]
    · rw [← neg_zero, le_neg] at fneg
      obtain ⟨r, hr⟩ := zStar.exists_nsmul_one_of_nonneg fneg
      rw [neg_eq_iff_eq_neg] at hr
      rw [hr]
      simp only [map_neg, map_nsmul, inclusion_one, AddSubgroup.coe_neg,
        AddSubmonoidClass.coe_nsmul, AddSubgroup.coe_toAddSubmonoid, smul_neg]
      simp only [AddSubgroupClass.coe_neg, AddSubmonoidClass.coe_nsmul, smul_neg, shift_neg]
      rw [← mul_nsmul, mul_nsmul', zStar.one_def, zStar.val_single,
          ← succ_pred (0 : Z), base_nsmul_single_succ_one_eq_single, shift_nsmul_comm,
          shift_single]
  · rw [Function.iterate_succ_apply', ← shift_nsmul_comm, IH]

lemma exists_shift_nsmul_one_of_nonneg {f : realHensel Z b} (hf : 0 ≤ f) :
    ∃ (k r : ℕ), shift^[k] (r • 1) = f := by
  obtain ⟨k, f', hk⟩ := zStar.fromRealHensel f
  have fpos : 0 ≤ f' := by
    rcases hf.eq_or_lt with rfl|hf
    · refine le_of_eq ?_
      induction' k with k IH generalizing f'
      · simp only [Nat.zero_eq, Function.iterate_zero, id_eq, ZeroMemClass.coe_zero,
        ZeroMemClass.coe_eq_zero] at hk
        rw [map_eq_zero_iff _ (AddSubgroup.inclusion_injective _)] at hk
        simp [hk]
      · refine IH _ ?_
        rw [Function.iterate_succ_apply'] at hk
        simp only [Subtype.ext_iff, val_shift, ZeroMemClass.coe_zero, shift_eq_zero] at hk
        rw [Subtype.ext_iff, hk]
        simp
    rw [← positive_iff, ← hk] at hf
    contrapose! hf
    rw [← zStar.negative_iff] at hf
    clear hk
    induction' k with k IH
    · exact hf.not_positive
    · contrapose! IH
      convert IH.leftShift using 1
      rw [Function.iterate_succ_apply', val_shift, leftInverse_leftShift_shift]
  obtain ⟨r, rfl⟩ := zStar.exists_nsmul_one_of_nonneg fpos
  refine ⟨k, r, ?_⟩
  ext : 1
  rw [←hk]
  clear hk
  induction' k with k IH
  · simp only [Nat.zero_eq, Function.iterate_zero, id_eq, AddSubmonoidClass.coe_nsmul]
    rfl
  · rw [Function.iterate_succ_apply', val_shift, IH, Function.iterate_succ_apply', val_shift]

lemma exists_shift_nsmul_one_of_nonpos {f : realHensel Z b} (hf : f ≤ 0) :
    ∃ (k r : ℕ), shift^[k] (r • 1) = -f := by
  refine exists_shift_nsmul_one_of_nonneg ?_
  simp [hf]

lemma shift_nsmul_comm (f : realHensel Z b) (n : ℕ) : shift (n • f) = n • shift f :=
  Subtype.ext (DigitExpansion.shift_nsmul_comm _ _)

@[elab_as_elim]
lemma shift_induction {motive : realHensel Z b → Prop}
    (h0 : motive 0)
    (hs : ∀ f, motive f → motive (f + 1))
    (hp : ∀ f, motive f → motive (f - 1))
    (hd : ∀ f, motive f → motive (shift f))
    (f : realHensel Z b) : motive f := by
  obtain ⟨k, f', hf⟩ := zStar.fromRealHensel f
  induction' k with k IH generalizing f f'
  · simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at hf
    revert f
    refine succArchimedeanRec ?_ ?_ ?_ f'
    · exact 0
    · intro f hf
      convert h0
      rw [Subtype.ext_iff, ← hf]
      simp
    · intro g IH f hf
      convert hs _ (IH (AddSubgroup.inclusion zStar_le_realHensel g) rfl)
      exact hf.symm
    · intro g IH f hf
      convert hp _ (IH (AddSubgroup.inclusion zStar_le_realHensel g) rfl)
      exact hf.symm
  · let g : realHensel Z b := ⟨real.leftShift ⟨f.val, f.prop.left⟩,
      (real.leftShift _).prop, leftShift_hensel f.prop.right⟩
    have hg : g.val = leftShift f.val := rfl
    rw [Function.iterate_succ', Function.comp_apply, Subtype.ext_iff,
        ← leftInverse_shift_leftShift.injective.eq_iff, val_shift,
        leftInverse_leftShift_shift, ← hg, ← Subtype.ext_iff] at hf
    specialize IH _ _ hf
    convert hd _ IH
    rw [Subtype.ext_iff, val_shift, hg, leftInverse_shift_leftShift]

end realHensel

end DigitExpansion
