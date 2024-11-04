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

lemma integerComplement.mem_iff {x : ℂ} : x ∈ ℂ_ℤ ↔ ¬ ∃ (n : ℤ), n = x := Iff.rfl

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ := by
 rw [integerComplement.mem_iff]
 simp only [not_exists]
 exact fun x a ↦ (UpperHalfPlane.ne_int z)  x (id (Eq.symm a))

lemma integerComplement.add_coe_int_mem {x : ℂ} (a : ℤ) : x + (a : ℂ) ∈ ℂ_ℤ ↔ x ∈ ℂ_ℤ := by
  constructor
  · contrapose
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, Decidable.not_not,
      forall_exists_index]
    intro b hb
    refine ⟨b + a, by simp only [Int.cast_add, hb]⟩
  · contrapose
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, Decidable.not_not,
      forall_exists_index]
    intro b hb
    refine ⟨b - a, by simp only [Int.cast_sub, hb, add_sub_cancel_right]⟩

lemma integerComplement.ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 0 :=
  fun hx' ↦ hx ⟨0, by exact_mod_cast hx'.symm⟩

lemma integerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ)  ≠ 0 :=
  integerComplement.ne_zero ((integerComplement.add_coe_int_mem a).mpr hx)

lemma integerComplement.ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ): x ≠ 1 :=
  fun hx' ↦ hx ⟨1, by exact_mod_cast hx'.symm⟩

end Complex
