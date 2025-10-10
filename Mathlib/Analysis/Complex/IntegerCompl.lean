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

/-- The complement of the integers in `ℂ` -/
def Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ" => integerComplement

lemma integerComplement_eq : ℂ_ℤ = {z : ℂ | ¬ ∃ (n : ℤ), n = z} := rfl

lemma integerComplement.mem_iff {x : ℂ} : x ∈ ℂ_ℤ ↔ ¬ ∃ (n : ℤ), n = x := Iff.rfl

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ :=
  not_exists.mpr fun x hx ↦ ne_int z x hx.symm

lemma integerComplement.add_coe_int_mem {x : ℂ} (a : ℤ) : x + (a : ℂ) ∈ ℂ_ℤ ↔ x ∈ ℂ_ℤ := by
  simp only [mem_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn ↦ ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn ↦ ⟨n + a, by simp [hn]⟩)⟩

lemma integerComplement.ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 0 :=
  fun hx' ↦ hx ⟨0, by exact_mod_cast hx'.symm⟩

lemma integerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ) ≠ 0 :=
  integerComplement.ne_zero ((integerComplement.add_coe_int_mem a).mpr hx)

lemma integerComplement.ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 1 :=
  fun hx' ↦ hx ⟨1, by exact_mod_cast hx'.symm⟩

lemma integerComplement_pow_two_ne_pow_two {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℤ) : x ^ 2 ≠ n ^ 2 := by
  have := not_exists.mp hx n
  have := not_exists.mp hx (-n)
  simp_all [sq_eq_sq_iff_eq_or_eq_neg, eq_comm]

lemma upperHalfPlane_inter_integerComplement :
    {z : ℂ | 0 < z.im} ∩ ℂ_ℤ = {z : ℂ | 0 < z.im} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
  exact fun hz ↦ UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩

end Complex
