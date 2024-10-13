/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

open UpperHalfPlane

/--The complement of the integers in `ℂ`. -/
def ComplexIntegerComplement := {z : ℂ // ¬ ∃ (n : ℤ), z = ↑n}

namespace ComplexIntegerComplement

local notation "ℂ_ℤ " => ComplexIntegerComplement

noncomputable instance : UniformSpace ℂ_ℤ := instUniformSpaceSubtype

theorem Complex.closedEmbedding_coe_complex : ClosedEmbedding ((↑) : ℤ → ℂ) := by
  apply Metric.closedEmbedding_of_pairwise_le_dist zero_lt_one
  convert Int.pairwise_one_le_dist
  simp_rw [dist_eq_norm]
  norm_cast
  rw [Int.norm_eq_abs]
  exact Int.cast_abs

lemma ℂ_ℤ_Isclosed : IsClosed (((↑) : ℤ → ℂ) '' ⊤) := by
  simp only [Set.top_eq_univ, Set.image_univ]
  exact Complex.closedEmbedding_coe_complex.isClosed_range

lemma ℂ_ℤ_IsOpen : IsOpen {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n} := by
  refine IsClosed.not ?_
  convert ℂ_ℤ_Isclosed
  ext y
  aesop

instance : LocallyCompactSpace ℂ_ℤ := IsOpen.locallyCompactSpace ℂ_ℤ_IsOpen

instance : Coe ℂ_ℤ ℂ := ⟨fun x => x.1⟩

lemma UpperHalfPlane.ne_int (z : ℍ) : ∀ n : ℤ, z.1 ≠ n := by
  intro n
  have h1 := z.2
  aesop

instance : Coe ℍ ℂ_ℤ := ⟨fun x => ⟨x, by simpa using UpperHalfPlane.ne_int x⟩⟩

lemma ℂ_ℤ_add_ne_zero (x : ℂ_ℤ) (a : ℤ) : x.1 + a ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg] at h
  have := not_exists.mp x.2 (-a)
  aesop

lemma ℂ_ℤ_not_zero (x : ℂ_ℤ) : x.1 ≠ 0 := by
  simpa using ℂ_ℤ_add_ne_zero x 0

end ComplexIntegerComplement
