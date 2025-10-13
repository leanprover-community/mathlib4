/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval

/-!
# Sharp bounds for sums of bounded finsets of integers

The sum of a finset of integers with cardinality `s` where all elements are at most `c` can be given
a sharper upper bound than `#s * c`, because the elements are distinct.

This file provides these sharp bounds, both in the upper-bounded and analogous lower-bounded cases.
-/


namespace Finset

/-- Sharp upper bound for the sum of a finset of integers that is bounded above, `Ioc` version. -/
lemma sum_le_sum_Ioc {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ x ∈ Ioc (c - #s) c, x := by
  set r := Ioc (c - #s) c
  calc
    _ ≤ ∑ x ∈ s ∩ r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_diff s r _]
      gcongr
      refine sum_le_card_nsmul _ _ _ fun x mx ↦ ?_
      rw [mem_sdiff, mem_Ioc, not_and'] at mx
      have := mx.2 (hs _ mx.1); omega
    _ = ∑ x ∈ r ∩ s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ioc, sub_sub_cancel, Int.toNat_natCast]
    _ ≤ _ := by
      rw [← sum_inter_add_sum_diff r s _]
      gcongr
      refine card_nsmul_le_sum _ _ _ fun x mx ↦ ?_
      rw [mem_sdiff, mem_Ioc] at mx; exact mx.1.1.le

/-- Sharp upper bound for the sum of a finset of integers that is bounded above, `range` version. -/
lemma sum_le_sum_range {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ n ∈ range #s, (c - n) := by
  convert sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ioc]; dsimp only; rw [mem_range] at mx; cutsat
  · intro x mx y my (h : c - x = c - y); cutsat
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ioc] at mx
    use (c - x).toNat; cutsat

/-- Sharp lower bound for the sum of a finset of integers that is bounded below, `Ico` version. -/
lemma sum_Ico_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ x ∈ Ico c (c + #s), x ≤ ∑ x ∈ s, x := by
  set r := Ico c (c + #s)
  calc
    _ ≤ ∑ x ∈ r ∩ s, x + #(r \ s) • (c + #s) := by
      rw [← sum_inter_add_sum_diff r s _]
      refine add_le_add_left (sum_le_card_nsmul _ _ _ fun x mx ↦ ?_) _
      rw [mem_sdiff, mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x ∈ s ∩ r, x + #(s \ r) • (c + #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
    _ ≤ _ := by
      rw [← sum_inter_add_sum_diff s r _]
      refine add_le_add_left (card_nsmul_le_sum _ _ _ fun x mx ↦ ?_) _
      rw [mem_sdiff, mem_Ico, not_and] at mx
      have := mx.2 (hs _ mx.1); omega

/-- Sharp lower bound for the sum of a finset of integers that is bounded below, `range` version. -/
lemma sum_range_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ n ∈ range #s, (c + n) ≤ ∑ x ∈ s, x := by
  convert sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ico]; dsimp only; rw [mem_range] at mx; cutsat
  · intro x mx y my (h : c + x = c + y); cutsat
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ico] at mx
    use (x - c).toNat; omega

end Finset
