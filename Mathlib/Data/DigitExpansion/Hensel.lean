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

end DigitExpansion
