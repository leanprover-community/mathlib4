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

* `rayleigh_compl`: Let `r` be a real number greater than 1.
  Then the complement of `B_r` is `B'_(r / (r - 1))`.
* `rayleigh_pos`: Let `r` be a real number greater than 1.
  Then every positive integer is in exactly one of `B⁺_r` or `B⁺'_(r / (r - 1))`.
* `rayleigh_irr_pos`: Let `r` be an irrational real number greater than 1.
  Then every positive integer is in exactly one of `B⁺_r` or `B⁺_(r / (r - 1))`.
* `rayleigh_compl'`, `rayleigh_pos'`, `rayleigh_irr_pos'`: The corresponding theorem that uses
  `Real.IsConjugateExponent r s` as a hypothesis.

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

variable {r : ℝ} (hr : r > 1) {j k : ℤ}

/-- Let `1 < r ∈ ℝ` and `s = r / (r - 1)`. Then `B_r` and `B'_s` are disjoint (i.e. no collision
exists). -/
theorem no_collision : Disjoint (beattySet r) (beattySet' r.conjugateExponent) := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  have hs := Real.one_lt_conjugateExponent hr
  have ⟨h₁₁, h₁₂⟩ : j / r ≤ k ∧ k < (j + 1) / r := by
    have hr := lt_trans zero_lt_one hr
    rw [beattySequence, Int.floor_eq_iff] at h₁
    exact ⟨(div_le_iff hr).2 h₁.1, (lt_div_iff hr).2 h₁.2⟩
  have ⟨h₂₁, h₂₂⟩ : j / r.conjugateExponent < m ∧ m ≤ (j + 1) / r.conjugateExponent := by
    have hs := lt_trans zero_lt_one hs
    rw [beattySequence', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
      add_sub_cancel] at h₂
    exact ⟨(div_lt_iff hs).2 h₂.1, (le_div_iff hs).2 h₂.2⟩
  have f (y : ℝ) : y / r + y / r.conjugateExponent = y := by
    have : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
    field_simp [Real.conjugateExponent, mul_sub_left_distrib]
  have h₃ : j < k + m := by
    have := add_lt_add_of_le_of_lt h₁₁ h₂₁
    rwa [f, ← Int.cast_add, Int.cast_lt] at this
  have h₄ : k + m ≤ j := by
    have := add_lt_add_of_lt_of_le h₁₂ h₂₂
    rwa [f, ← Int.cast_add, ← Int.cast_one, ← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at this
  have := lt_of_le_of_lt' h₄ h₃
  exact (lt_self_iff_false j).1 this

/-- Let `1 < r ∈ ℝ` and `s = r / (r - 1)`. Suppose there is an integer `j` where `B_r` and `B'_s`
both jump over `j` (i.e. an anti-collision). Then this leads to a contradiction. -/
theorem no_anticollision :
    ¬∃ (j k m : ℤ), k * r < j ∧ j + 1 ≤ (k + 1) * r ∧
      m * r.conjugateExponent ≤ j ∧ j + 1 < (m + 1) * r.conjugateExponent := by
  have hr₀ : r > 0 := lt_trans zero_lt_one hr
  have hs₀ : r.conjugateExponent > 0 := lt_trans zero_lt_one (Real.one_lt_conjugateExponent hr)
  have f (y : ℝ) : y / r + y / r.conjugateExponent = y := by
    have : r ≠ 0 := ne_of_gt hr₀
    field_simp [Real.conjugateExponent, mul_sub_left_distrib]
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₁₁ := (lt_div_iff hr₀).2 h₁₁
  have h₁₂ := (div_le_iff hr₀).2 h₁₂
  have h₂₁ := (le_div_iff hs₀).2 h₂₁
  have h₂₂ := (div_lt_iff hs₀).2 h₂₂
  have h₃ : k + m < j := by
    have := add_lt_add_of_lt_of_le h₁₁ h₂₁
    rwa [f, ← Int.cast_add, Int.cast_lt] at this
  have h₄ : j ≤ k + m := by
    have := add_lt_add_of_le_of_lt h₁₂ h₂₂
    rw [f, ← Int.cast_one] at this
    simp_rw [← Int.cast_add, Int.cast_lt] at this
    rwa [← add_assoc, add_lt_add_iff_right, add_right_comm, Int.lt_add_one_iff] at this
  have := lt_of_le_of_lt h₄ h₃
  exact (lt_self_iff_false j).1 this

/-- Let `1 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`.

This is unfortunately not in the proof sketch. -/
theorem hit_or_miss : j ∈ beattySet r ∨ (∃ k : ℤ, k * r < j ∧ j + 1 ≤ (k + 1) * r) := by
  have hr₀ : r > 0 := lt_trans zero_lt_one hr
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, by simpa, ?_⟩
    rw [Int.cast_sub, Int.cast_one, sub_add_cancel, ← div_le_iff hr₀]
    apply Int.le_ceil
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySequence, Int.floor_eq_iff]
    constructor
    · simpa
    rw [Int.cast_sub, Int.cast_one, ← lt_div_iff hr₀, sub_lt_iff_lt_add]
    apply Int.ceil_lt_add_one

/-- Let `1 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B'_r` or `B'_r` jumps over `j`.

This is unfortunately not in the proof sketch. -/
theorem hit_or_miss' : j ∈ beattySet' r ∨ (∃ k : ℤ, k * r ≤ j ∧ j + 1 < (k + 1) * r) := by
  have hr₀ : r > 0 := lt_trans zero_lt_one hr
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · refine Or.inr ⟨⌊(j + 1) / r⌋, ‹_›, ?_⟩
    rw [← div_lt_iff hr₀]
    apply Int.lt_floor_add_one
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySequence', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one]
    constructor
    · rwa [add_sub_cancel]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) hr₀)

end Beatty

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1. Then the complement of `B_r` is `B'_(r / (r - 1))`. -/
theorem rayleigh_compl {r : ℝ} (hr : r > 1) : (beattySet r)ᶜ = beattySet' r.conjugateExponent := by
  ext j
  by_cases h₁ : j ∈ beattySet r
  · by_cases h₂ : j ∈ beattySet' r.conjugateExponent
    · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hr)).elim
    · simp [Set.compl, h₁, h₂]
  · by_cases h₂ : j ∈ beattySet' r.conjugateExponent
    · simp [Set.compl, h₁, h₂]
    · have hs := Real.one_lt_conjugateExponent hr
      have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hr).resolve_left h₁
      have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hs).resolve_left h₂
      exact (Beatty.no_anticollision hr ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim

/-- A version of `rayleigh_compl` that uses `Real.IsConjugateExponent r s` as a hypothesis. -/
theorem rayleigh_compl' {r s : ℝ} (hr : Real.IsConjugateExponent r s) :
    (beattySet r)ᶜ = beattySet' s := by
  convert @rayleigh_compl _ hr.one_lt
  exact hr.conj_eq

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1. Then every positive integer is in exactly one of `B⁺_r` or `B⁺'_(r / (r - 1))`. -/
theorem rayleigh_pos {r : ℝ} (hr : r > 1) :
    ∀ {j : ℤ}, j > 0 →
      (j ∈ beattySetPos r ∧ j ∉ beattySetPos' r.conjugateExponent) ∨
      (j ∉ beattySetPos r ∧ j ∈ beattySetPos' r.conjugateExponent) := by
  intro j hj
  have hb₁ : ∀ s ≥ 0, j ∈ beattySetPos s ↔ j ∈ beattySet s := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySequence, gt_iff_lt, Int.floor_pos] at hj
    have := pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one hj) hs
    rwa [Int.cast_pos] at this
  have hb₂ : ∀ s ≥ 0, j ∈ beattySetPos' s ↔ j ∈ beattySet' s := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySequence', gt_iff_lt, lt_sub_iff_add_lt, zero_add] at hj
    have hj := Int.ceil_pos.1 (lt_trans zero_lt_one hj)
    have := pos_of_mul_pos_left hj hs
    rwa [Int.cast_pos] at this
  rw [hb₁ _ (lt_trans zero_lt_one hr).le,
    hb₂ _ (lt_trans zero_lt_one (Real.one_lt_conjugateExponent hr)).le, ← rayleigh_compl hr,
    Set.not_mem_compl_iff, Set.mem_compl_iff, and_self, and_self]
  exact or_not

/-- A version of `rayleigh_pos` that uses `Real.IsConjugateExponent r s` as a hypothesis. -/
theorem rayleigh_pos' {r s : ℝ} (hr : Real.IsConjugateExponent r s) :
    ∀ {j : ℤ}, j > 0 →
      (j ∈ beattySetPos r ∧ j ∉ beattySetPos' s) ∨ (j ∉ beattySetPos r ∧ j ∈ beattySetPos' s) := by
  convert @rayleigh_pos _ hr.one_lt <;> exact hr.conj_eq

/-- Rayleigh's theorem on Beatty sequences. Let `r` be an irrational real number greater than 1.
Then every positive integer is in exactly one of `B⁺_r` or `B⁺_(r / (r - 1))`. -/
theorem rayleigh_irr_pos {r : ℝ} (hr₁ : r > 1) (hr₂ : Irrational r) :
    ∀ {j : ℤ}, j > 0 →
      (j ∈ beattySetPos r ∧ j ∉ beattySetPos r.conjugateExponent) ∨
      (j ∉ beattySetPos r ∧ j ∈ beattySetPos r.conjugateExponent) := by
  intro j hj
  have hb : ∀ s, Irrational s → (j ∈ beattySetPos s ↔ j ∈ beattySetPos' s) := by
    intro s hs_irr
    dsimp only [beattySetPos, beattySequence, beattySetPos', beattySequence']
    congr! 5; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
    symm; rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel]
    refine ⟨lt_of_le_of_ne (Int.floor_le _) fun h ↦ ?_, (Int.lt_floor_add_one _).le⟩
    exact Irrational.ne_int (hs_irr.int_mul hk.ne') ⌊k * s⌋ h.symm
  have hs_irr : Irrational r.conjugateExponent := by
    convert ((hr₂.sub_int 1).int_div one_ne_zero).int_add 1 using 1
    rw [Int.cast_one, add_div', one_mul, sub_add_cancel, Real.conjugateExponent]
    exact ne_of_gt (sub_pos.2 hr₁)
  rw [hb _ hs_irr]
  exact rayleigh_pos hr₁ hj

/-- A version of `rayleigh_irr_pos` that uses `Real.IsConjugateExponent r s` as a hypothesis. -/
theorem rayleigh_irr_pos' {r s : ℝ} (hr₁ : Real.IsConjugateExponent r s) (hr₂ : Irrational r) :
    ∀ {j : ℤ}, j > 0 →
      (j ∈ beattySetPos r ∧ j ∉ beattySetPos s) ∨ (j ∉ beattySetPos r ∧ j ∈ beattySetPos s) := by
  convert @rayleigh_irr_pos _ hr₁.one_lt hr₂ <;> exact hr₁.conj_eq
