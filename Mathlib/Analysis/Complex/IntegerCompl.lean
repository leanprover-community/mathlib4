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
abbrev Complex.IntegerComplement := {z : ℂ | ¬ ∃ (n : ℤ), z = ↑n}

namespace Complex

local notation "ℂ_ℤ " => IntegerComplement

instance : IsOpen ℂ_ℤ := by
  convert Complex.isOpen_compl_range_intCast
  rw [IntegerComplement]
  aesop

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ := by
  simpa using UpperHalfPlane.ne_int z

lemma IntegerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ)  ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg] at h
  have := not_exists.mp hx (-a)
  aesop

lemma IntegerComplement_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : (x : ℂ) ≠ (0 : ℂ) := by
  simpa using IntegerComplement_add_ne_zero hx 0

lemma IntegerComplement_ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ): x.1 ≠ 1 := by
  have := IntegerComplement_add_ne_zero hx (-1 : ℤ)
  aesop

end Complex
