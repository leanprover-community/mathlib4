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

end DigitExpansion
