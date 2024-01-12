/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.DigitExpansion.Integer.Basic

/-!
# Defining reals without the use of rationals, multiplicative structure of rationals and integers

* [Defining reals without the use of rationals][debruijn1976]

-/

variable {Z : Type*} [Nonempty Z] [LinearOrder Z] [SuccOrder Z] [NoMaxOrder Z] [PredOrder Z]
  [NoMinOrder Z] [IsSuccArchimedean Z] [Zero Z] {b : ℕ} [hb : NeZero b]
  [∀ (f g : DigitExpansion Z b) z, Decidable (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y)]

open Order

namespace DigitExpansion.realHensel

@[simp]
lemma iterate_shift_zero (k : ℕ) :
    shift^[k] (0 : realHensel Z b) = 0 := by
  induction' k with k IH
  · simp
  · simp only [Function.iterate_succ_apply', IH, Subtype.ext_iff, val_shift]
    simp [val_iterate_shift]

lemma iterate_shift_add (x y : realHensel Z b) (k : ℕ) :
    shift^[k] (x + y) = shift^[k] x + shift^[k] y := by
  induction' k with k IH
  · simp
  · simp only [Function.iterate_succ_apply', IH, Subtype.ext_iff, val_shift]
    simp [val_iterate_shift, val_shift, shift_add]

lemma iterate_shift_nsmul_comm (f : realHensel Z b) (k n : ℕ) :
    shift^[k] (n • f) = n • shift^[k] f := by
  induction n
  case zero => simp
  case succ n IH => simp [succ_nsmul, iterate_shift_add, IH]

lemma iterate_shift_neg (x : realHensel Z b) (k : ℕ) : shift^[k] (-x) = - shift^[k] x := by
  induction' k with k IH
  · simp
  · simp only [Function.iterate_succ_apply', IH, Subtype.ext_iff, val_shift]
    simp only [AddSubgroupClass.coe_neg, val_iterate_shift, val_shift, shift_neg]

lemma shift_add_hom_comm {F : Type*} [AddMonoidHomClass F (realHensel Z b) (realHensel Z b)]
    (T : F) (x : realHensel Z b) : shift (T x) = T (shift x) := by
  rw [← base_nsmul_shift_eq x, map_nsmul, shift_nsmul_comm, base_nsmul_shift_eq,
      base_nsmul_shift_eq]

lemma iterate_shift_add_hom_comm {F : Type*} [AddMonoidHomClass F (realHensel Z b) (realHensel Z b)]
    (T : F) (x : realHensel Z b) (k : ℕ) : shift^[k] (T x) = T (shift^[k] x) := by
  induction' k with k IH
  · simp
  · simp only [Function.iterate_succ_apply', IH, shift_add_hom_comm]

lemma unique_add_hom (h : realHensel Z b) :
    ∃! (T : realHensel Z b →+ realHensel Z b), T 1 = h := by
  obtain ⟨k, f', hk⟩ := zStar.fromRealHensel h
  rcases le_total 0 f' with fpos|fneg
  · obtain ⟨r, rfl⟩ := zStar.exists_nsmul_one_of_nonneg fpos
    refine ⟨⟨⟨fun x ↦ shift^[k] (r • x), ?_⟩, ?_⟩, ?_, ?_⟩
    · simp
    · intros
      simp [iterate_shift_add, nsmul_add]
    · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      simp [← hk, ← realHensel.one_def]
    · simp only [← hk]
      intro U hU
      ext x : 1
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      cases' le_total 0 x with xpos xneg
      · obtain ⟨l, s, rfl⟩ := exists_shift_nsmul_one_of_nonneg xpos
        rw [← iterate_shift_add_hom_comm, map_nsmul, hU]
        simp only [map_nsmul, iterate_shift_nsmul_comm, ← mul_nsmul, mul_comm,
                   ← Function.iterate_add_apply, add_comm, realHensel.one_def]
      · rw [← neg_neg x, map_neg]
        obtain ⟨l, s, hx⟩ := exists_shift_nsmul_one_of_nonpos xneg
        rw [← hx, iterate_shift_nsmul_comm _ k, ← iterate_shift_add_hom_comm, map_nsmul, hU,
            ← iterate_shift_nsmul_comm, iterate_shift_neg, ← Function.iterate_add_apply,
            ← Function.iterate_add_apply, neg_nsmul]
        simp only [map_nsmul, iterate_shift_nsmul_comm, ← mul_nsmul, mul_comm,
                   ← Function.iterate_add_apply, add_comm, realHensel.one_def]
  · rw [← neg_zero, le_neg] at fneg
    obtain ⟨r, hr⟩ := zStar.exists_nsmul_one_of_nonneg fneg
    rw [neg_eq_iff_eq_neg] at hr
    refine ⟨⟨⟨fun x ↦ shift^[k] (r • - x), ?_⟩, ?_⟩, ?_, ?_⟩
    · simp
    · intros
      simp only [neg_add_rev, nsmul_add, smul_neg, iterate_shift_add, iterate_shift_neg]
      exact add_comm _ _
    · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      simp [← hk, ← realHensel.one_def, hr]
    · simp only [smul_neg, ← hk, hr]
      clear hk hr
      intro U hU
      ext x : 1
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      cases' le_total 0 x with xpos xneg
      · obtain ⟨l, s, rfl⟩ := exists_shift_nsmul_one_of_nonneg xpos
        rw [← iterate_shift_add_hom_comm, map_nsmul, hU]
        simp only [map_nsmul, iterate_shift_nsmul_comm, ← mul_nsmul, mul_comm, iterate_shift_neg,
                   ← Function.iterate_add_apply, add_comm, realHensel.one_def, map_neg,
                   neg_nsmul]
      · rw [← neg_neg x, map_neg]
        obtain ⟨l, s, hx⟩ := exists_shift_nsmul_one_of_nonpos xneg
        rw [← hx, iterate_shift_neg, iterate_shift_nsmul_comm _ k, ← iterate_shift_add_hom_comm,
            map_nsmul, hU, ← iterate_shift_nsmul_comm, iterate_shift_neg,
            ← Function.iterate_add_apply, ← Function.iterate_add_apply, neg_nsmul]
        simp only [map_nsmul, iterate_shift_nsmul_comm, ← mul_nsmul, mul_comm, map_neg,
                   ← Function.iterate_add_apply, add_comm, realHensel.one_def, neg_nsmul,
                   iterate_shift_neg]

end DigitExpansion.realHensel
