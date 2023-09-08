/-
Copyright (c) 2023 Jason Yuen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Yuen
-/
import Mathlib.Data.Real.Irrational

/-!
# Rayleigh's theorem on Beatty sequences

This file proves Rayleigh's theorem on Beatty sequences.

## Main statements

* `beattySequence`: The Beatty sequence for real number `r` is defined to be
  `B_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`.
* `rayleigh`: Rayleigh's theorem on Beatty sequences. Let `r` be an irrational real number greater
  than 1. Then every positive integer is in exactly one of `B_r` or `B_(r / (r - 1))`.

## References

* [Wikipedia, *Beatty sequence*](https://en.wikipedia.org/wiki/Beatty_sequence)

## Tags

beatty, sequence, rayleigh, irrational, floor
-/

/-- The Beatty sequence for real number `r` is defined to be `B_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`. -/
def beattySequence (r : ℝ) : Set ℤ :=
  { j | ∃ k : ℤ, k > 0 ∧ j = ⌊k * r⌋ }

namespace Beatty

variable {r} (hr₁ : r > 1) (hr₂ : Irrational r) {j k : ℤ} (hj : j > 0)

theorem irrational_s :
    r / (r - 1) > 1 ∧ Irrational (r / (r - 1)) := by
  constructor
  · apply (lt_div_iff (sub_pos.2 hr₁)).2
    rw [one_mul]
    exact sub_one_lt r
  · convert ((hr₂.sub_int 1).int_div one_ne_zero).int_add 1 using 1
    rw [Int.cast_one, add_div', one_mul, sub_add_cancel]
    exact ne_of_gt (sub_pos.2 hr₁)

theorem irrational_aux (hj : j ≠ 0) : (j : ℝ) ≠ k * r := by
  intro h
  have hk : k ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul, Int.cast_eq_zero] at h
    exact hj h
  have := hr₂.int_mul hk
  rw [← h] at this
  exact (j.not_irrational this).elim

theorem no_collision_aux (h : j = ⌊k * r⌋) : j / r < k ∧ k < (j + 1) / r := by
  have hr₁ := lt_trans zero_lt_one hr₁
  have ⟨h₁, h₂⟩ := Int.floor_eq_iff.1 h.symm
  have h₁ := lt_of_le_of_ne h₁ (irrational_aux hr₂ hj.ne.symm)
  exact ⟨(div_lt_iff hr₁).2 h₁, (lt_div_iff hr₁).2 h₂⟩

/-- Let `1 < r ∈ ℝ ∖ ℚ` and `s = r / (r - 1)`. Suppose there are integers `j > 0`, `k`, `m` such
that `j = ⌊k * r⌋ = ⌊m * s⌋` (i.e. a collision). Then this leads to a contradiction. -/
theorem no_collision : ¬∃ (j k m : ℤ), j > 0 ∧ j = ⌊k * r⌋ ∧ j = ⌊m * (r / (r - 1))⌋ := by
  intro ⟨j, k, m, hj, h₁, h₂⟩
  have ⟨hs₁, hs₂⟩ := irrational_s hr₁ hr₂
  have ⟨h₁₁, h₁₂⟩ := no_collision_aux hr₁ hr₂ hj h₁
  have ⟨h₂₁, h₂₂⟩ := no_collision_aux hs₁ hs₂ hj h₂
  have f (y : ℝ) : y / r + y / (r / (r - 1)) = y := by
    have : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr₁)
    field_simp [mul_sub_left_distrib]
  have h₃ : j < k + m := by
    have := add_lt_add_of_lt_of_lt h₁₁ h₂₁
    rwa [f, ← Int.cast_add, Int.cast_lt] at this
  have h₄ : k + m ≤ j := by
    have := add_lt_add_of_lt_of_lt h₁₂ h₂₂
    rwa [f, ← Int.cast_add, ← Int.cast_one, ← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at this
  have := lt_of_le_of_lt' h₄ h₃
  exact (lt_self_iff_false j).1 this

/-- Let `1 < r ∈ ℝ ∖ ℚ` and `s = r / (r - 1)`. Suppose there is an integer `j > 0` where `B_r` and
`B_s` both jump over `j` (i.e. an anti-collision). Then this leads to a contradiction. -/
theorem no_anticollision :
    ¬∃ (j k m : ℤ), j > 0 ∧ k * r < j ∧ j + 1 ≤ (k + 1) * r ∧
      m * (r / (r - 1)) < j ∧ j + 1 ≤ (m + 1) * (r / (r - 1)) := by
  have ⟨hs₁, hs₂⟩ := irrational_s hr₁ hr₂
  have f (y : ℝ) : y / r + y / (r / (r - 1)) = y := by
    have : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr₁)
    field_simp [mul_sub_left_distrib]
  intro ⟨j, k, m, hj, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have hj₁ : j + 1 ≠ 0 := by
    intro h
    have := lt_add_one j
    rw [h] at this
    exact (lt_self_iff_false 0).1 (lt_trans hj this)
  have h₁₂ := lt_of_le_of_ne h₁₂ <| by
    convert irrational_aux (k := k + 1) hr₂ hj₁ <;> norm_num
  have h₂₂ := lt_of_le_of_ne h₂₂ <| by
    convert irrational_aux (k := m + 1) hs₂ hj₁ <;> norm_num
  have h₁₁ := (lt_div_iff (lt_trans zero_lt_one hr₁)).2 h₁₁
  have h₁₂ := (div_lt_iff (lt_trans zero_lt_one hr₁)).2 h₁₂
  have h₂₁ := (lt_div_iff (lt_trans zero_lt_one hs₁)).2 h₂₁
  have h₂₂ := (div_lt_iff (lt_trans zero_lt_one hs₁)).2 h₂₂
  have h₃ : k + m < j := by
    have := add_lt_add_of_lt_of_lt h₁₁ h₂₁
    rwa [f, ← Int.cast_add, Int.cast_lt] at this
  have h₄ : j ≤ k + m := by
    have := add_lt_add_of_lt_of_lt h₁₂ h₂₂
    rw [f, ← Int.cast_one] at this
    simp_rw [← Int.cast_add, Int.cast_lt] at this
    rwa [← add_assoc, add_lt_add_iff_right, add_right_comm, Int.lt_add_one_iff] at this
  have := lt_of_le_of_lt h₄ h₃
  exact (lt_self_iff_false j).1 this

/-- Let `1 < r ∈ ℝ ∖ ℚ` and `0 < j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`.

This is unfortunately not in the proof sketch. -/
theorem hit_or_miss : j ∈ beattySequence r ∨ (∃ k : ℤ, k * r < j ∧ j + 1 ≤ (k + 1) * r) := by
  have hr₀ : r > 0 := lt_trans zero_lt_one hr₁
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  have h₁ := Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) hr₀
  rw [le_sub_iff_add_le, zero_add] at h₁
  have h₁ := lt_of_le_of_ne h₁ <| by
    have hj₁ : j + 1 ≠ 0 := by
      intro h
      have := lt_add_one j
      rw [h] at this
      exact (lt_self_iff_false 0).1 (lt_trans hj this)
    symm; convert irrational_aux hr₂ hj₁; norm_num
  cases' lt_or_ge ((⌊(j + 1) / r⌋) * r) j with h₂ h₂
  · refine Or.inr ⟨⌊(j + 1) / r⌋, h₂, ?_⟩
    have := Int.sub_floor_div_mul_lt (j + 1 : ℝ) hr₀
    rw [sub_lt_iff_lt_add, ← one_add_mul (α := ℝ), add_comm (a := 1)] at this
    exact this.le
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_, ?_⟩
    · have hj' : (j : ℝ) > 0 := by norm_num; exact hj
      have := lt_of_le_of_lt' h₂ hj'
      have := (pos_iff_pos_of_mul_pos this).2 hr₀
      norm_num at this
      exact this
    · symm; rw [Int.floor_eq_iff]; exact ⟨h₂, h₁⟩

end Beatty

/-- Rayleigh's theorem on Beatty sequences. Let `r` be an irrational real number greater than 1.
Then every positive integer is in exactly one of `B_r` or `B_(r / (r - 1))`. -/
theorem rayleigh {r : ℝ} (hr₁ : r > 1) (hr₂ : Irrational r) :
    ∀ {j : ℤ}, j > 0 →
      (j ∈ beattySequence r ∧ j ∉ beattySequence (r / (r - 1))) ∨
      (j ∉ beattySequence r ∧ j ∈ beattySequence (r / (r - 1))) := by
  intro j hj
  by_cases h₁ : j ∈ beattySequence r
  · by_cases h₂ : j ∈ beattySequence (r / (r - 1))
    · have ⟨k, _, h₃⟩ := h₁
      have ⟨m, _, h₄⟩ := h₂
      exact (Beatty.no_collision hr₁ hr₂ ⟨j, k, m, hj, h₃, h₄⟩).elim
    · exact Or.inl ⟨h₁, h₂⟩
  · by_cases h₂ : j ∈ beattySequence (r / (r - 1))
    · exact Or.inr ⟨h₁, h₂⟩
    · have ⟨hs₁, hs₂⟩ := Beatty.irrational_s hr₁ hr₂
      have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hr₁ hr₂ hj).resolve_left h₁
      have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss hs₁ hs₂ hj).resolve_left h₂
      exact (Beatty.no_anticollision hr₁ hr₂ ⟨j, k, m, hj, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim
