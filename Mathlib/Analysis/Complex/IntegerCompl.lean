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
abbrev Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ " => integerComplement

lemma IntegerComplement_eq : ℂ_ℤ = {z : ℂ | ¬ ∃ (n : ℤ), n = z} := rfl

lemma IntegerComplement_not_exist {x : ℂ} (hx : x ∈ ℂ_ℤ) : ¬ ∃ (n : ℤ), n = x := by
  rw [IntegerComplement_eq] at hx
  exact hx

lemma IntegerComplement_mk {x : ℂ} (hx : ¬ ∃ (n : ℤ), n = x) : x ∈ ℂ_ℤ := by
  rw [IntegerComplement_eq]
  exact hx

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ := by
 apply IntegerComplement_mk
 simp only [not_exists]
 exact fun x a ↦ (UpperHalfPlane.ne_int z)  x (id (Eq.symm a))

lemma IntegerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ)  ≠ 0 := by
  intro h
  rw [add_eq_zero_iff_eq_neg] at h
  have := not_exists.mp hx (-a)
  aesop

lemma IntegerComplement_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 0 := by
  simpa using IntegerComplement_add_ne_zero hx 0

lemma IntegerComplement_ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ): x ≠ 1 := by
  have := IntegerComplement_add_ne_zero hx (-1 : ℤ)
  aesop

end Complex
