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

instance : LocallyCompactSpace ℂ_ℤ := by
  apply IsOpen.locallyCompactSpace
  convert Complex.isOpen_compl_range_intCast
  simp only [Set.mem_range, eq_comm]

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
