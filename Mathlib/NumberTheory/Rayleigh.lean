/-
Copyright (c) 2023 Jason Yuen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Yuen
-/
import Mathlib.Data.Real.ConjugateExponents
import Mathlib.Data.Real.Irrational

/-!
# Rayleigh's theorem on Beatty sequences

This file proves Rayleigh's theorem on Beatty sequences. We start by proving `rayleigh_compl`, which
is a generalization of Rayleigh's theorem, and eventually prove `rayleigh_irr_pos`, which is
Rayleigh's theorem.

## Main definitions

* `beattySequence`: In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`.
* `beattySequence'`: In this variant of the Beatty sequence for `r`, the `k`th term is
  `⌈k * r⌉ - 1`.
* `beattySet`: Define the Beatty set for `r ∈ ℝ` to be `B_r := {⌊k * r⌋ | k ∈ ℤ}`.
* `beattySet'`: Define another Beatty set for `r ∈ ℝ` to be `B'_r := {⌈k * r⌉ - 1 | k ∈ ℤ}`.
* `beattySetPos`: Define the positive Beatty set for `r ∈ ℝ` to be `B⁺_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`.
* `beattySetPos'`: Define another positive Beatty set for `r ∈ ℝ` to be
  `B⁺'_r := {⌈r⌉-1, ⌈2r⌉-1, ⌈3r⌉-1, ...}`.

## Main statements

* `rayleigh_compl`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then the complement of `B_r` is `B'_s`.
* `rayleigh_pos`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then `B⁺_r` and `B⁺'_s` partition the positive integers.
* `rayleigh_irr_pos`: Let `r` be an irrational number greater than 1, and `1/r + 1/s = 1`.
  Then `B⁺_r` and `B⁺_s` partition the positive integers.

## References

* [Wikipedia, *Beatty sequence*](https://en.wikipedia.org/wiki/Beatty_sequence)

## Tags

beatty, sequence, rayleigh, irrational, floor, positive
-/

/-- In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`. -/
noncomputable def beattySequence (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌊k * r⌋

/-- In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`. -/
noncomputable def beattySequence' (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌈k * r⌉ - 1

/-- Define the Beatty set for `r ∈ ℝ` to be `B_r := {⌊k * r⌋ | k ∈ ℤ}`. -/
def beattySet (r : ℝ) : Set ℤ :=
  { beattySequence r k | k }

/-- Define another Beatty set for `r ∈ ℝ` to be `B'_r := {⌈k * r⌉ - 1 | k ∈ ℤ}`. -/
def beattySet' (r : ℝ) : Set ℤ :=
  { beattySequence' r k | k }

/-- Define the positive Beatty set for `r ∈ ℝ` to be `B⁺_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`. -/
def beattySetPos (r : ℝ) : Set ℤ :=
  { beattySequence r k | k > 0 }

/-- Define another positive Beatty set for `r ∈ ℝ` to be `B⁺'_r := {⌈r⌉-1, ⌈2r⌉-1, ⌈3r⌉-1, ...}`. -/
def beattySetPos' (r : ℝ) : Set ℤ :=
  { beattySequence' r k | k > 0 }

namespace Beatty

variable {r s : ℝ} (hrs : r.IsConjugateExponent s) {j k : ℤ}

/-- Let `r > 1` and `1/r + 1/s = 1`. Then `B_r` and `B'_s` are disjoint (i.e. no collision exists).
-/
theorem no_collision : Disjoint (beattySet r) (beattySet' s) := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySequence, Int.floor_eq_iff, ← div_le_iff hrs.pos, ← lt_div_iff hrs.pos] at h₁
  rw [beattySequence', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel, ← div_lt_iff hrs.symm.pos, ← le_div_iff hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [← inv_mul_eq_div, ← right_distrib, inv_eq_one_div, hrs.inv_add_inv_conj,
    one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact (lt_self_iff_false _).1 (lt_of_le_of_lt' h₄ h₃)

/-- Let `r > 1` and `1/r + 1/s = 1`. Suppose there is an integer `j` where `B_r` and `B'_s` both
jump over `j` (i.e. an anti-collision). Then this leads to a contradiction. -/
theorem no_anticollision :
    ¬∃ (j k m : ℤ), k * r < j ∧ j + 1 ≤ (k + 1) * r ∧ m * s ≤ j ∧ j + 1 < (m + 1) * s := by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₁₁ := (lt_div_iff hrs.pos).2 h₁₁
  have h₁₂ := (div_le_iff hrs.pos).2 h₁₂
  have h₂₁ := (le_div_iff hrs.symm.pos).2 h₂₁
  have h₂₂ := (div_lt_iff hrs.symm.pos).2 h₂₂
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [← inv_mul_eq_div, ← right_distrib, inv_eq_one_div, hrs.inv_add_inv_conj,
    one_mul] at h₃ h₄
  rw [← Int.cast_one, ← add_assoc, add_lt_add_iff_right, add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact (lt_self_iff_false _).1 (lt_of_le_of_lt' h₄ h₃)

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`. -/
theorem hit_or_miss (h : r > 0) : j ∈ beattySet r ∨ (∃ k : ℤ, k * r < j ∧ j + 1 ≤ (k + 1) * r) := by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, by simpa, ?_⟩
    rw [Int.cast_sub, Int.cast_one, sub_add_cancel, ← div_le_iff h]
    apply Int.le_ceil
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySequence, Int.floor_eq_iff]
    constructor
    · simpa
    rw [Int.cast_sub, Int.cast_one, ← lt_div_iff h, sub_lt_iff_lt_add]
    apply Int.ceil_lt_add_one

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B'_r` or `B'_r` jumps over `j`. -/
theorem hit_or_miss' (h : r > 0) :
    j ∈ beattySet' r ∨ (∃ k : ℤ, k * r ≤ j ∧ j + 1 < (k + 1) * r) := by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · refine Or.inr ⟨⌊(j + 1) / r⌋, ‹_›, ?_⟩
    rw [← div_lt_iff h]
    apply Int.lt_floor_add_one
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySequence', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one]
    constructor
    · rwa [add_sub_cancel]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) h)

end Beatty

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then the complement of `B_r` is `B'_s`. -/
theorem rayleigh_compl {r s : ℝ} (hrs : r.IsConjugateExponent s) :
    (beattySet r)ᶜ = beattySet' s := by
  ext j
  by_cases h₁ : j ∈ beattySet r
  · by_cases h₂ : j ∈ beattySet' s
    · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
    · simp [Set.compl, h₁, h₂]
  · by_cases h₂ : j ∈ beattySet' s
    · simp [Set.compl, h₁, h₂]
    · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
      have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
      exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺'_s` partition the positive integers. -/
theorem rayleigh_pos {r s : ℝ} (hrs : r.IsConjugateExponent s) :
    beattySetPos r ∆ beattySetPos' s = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · intro j hj
    rcases Set.mem_of_mem_of_subset hj Set.symmDiff_subset_union with ⟨k, hk, hjk⟩ | ⟨k, hk, hjk⟩
    · rw [Set.mem_setOf_eq, ← hjk, beattySequence, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.one_lt.le
    · rw [Set.mem_setOf_eq, ← hjk, beattySequence', ← Int.ceil_sub_one, Int.ceil_pos, sub_pos]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.one_lt
  intro j (hj : 0 < j)
  have hb₁ : ∀ s ≥ 0, j ∈ beattySetPos s ↔ j ∈ beattySet s := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySequence, Int.floor_pos] at hj
    have := pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one hj) hs
    rwa [Int.cast_pos] at this
  have hb₂ : ∀ s ≥ 0, j ∈ beattySetPos' s ↔ j ∈ beattySet' s := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySequence', lt_sub_iff_add_lt, zero_add] at hj
    have hj := Int.ceil_pos.1 (lt_trans zero_lt_one hj)
    have := pos_of_mul_pos_left hj hs
    rwa [Int.cast_pos] at this
  rw [Set.mem_symmDiff, hb₁ _ hrs.nonneg, hb₂ _ hrs.symm.nonneg, ← rayleigh_compl hrs,
    Set.not_mem_compl_iff, Set.mem_compl_iff, and_self, and_self]
  exact or_not

/-- Rayleigh's theorem on Beatty sequences. Let `r` be an irrational number greater than 1, and
`1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers. -/
theorem rayleigh_irr_pos {r s : ℝ} (hrs : r.IsConjugateExponent s) (hr : Irrational r) :
    beattySetPos r ∆ beattySetPos s = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · intro j hj
    rcases Set.mem_of_mem_of_subset hj Set.symmDiff_subset_union with
      ⟨k, hk, hjk⟩ | ⟨k, hk, hjk⟩ <;>
      rw [Set.mem_setOf_eq, ← hjk, beattySequence, Int.floor_pos] <;>
      apply one_le_mul_of_one_le_of_one_le (by norm_cast) <;>
      [exact hrs.one_lt.le; exact hrs.symm.one_lt.le]
  intro j hj
  have hs : Irrational s := by
    convert ((hr.sub_int 1).int_div one_ne_zero).int_add 1
    rw [Int.cast_one, add_div' _ _ _ hrs.sub_one_ne_zero, one_mul, sub_add_cancel, hrs.conj_eq]
  have hb : beattySetPos s = beattySetPos' s := by
    dsimp only [beattySetPos, beattySequence, beattySetPos', beattySequence']
    congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
    symm; rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel]
    refine ⟨lt_of_le_of_ne (Int.floor_le _) fun h ↦ ?_, (Int.lt_floor_add_one _).le⟩
    exact Irrational.ne_int (hs.int_mul hk.ne') ⌊k * s⌋ h.symm
  rwa [hb, rayleigh_pos hrs]
