/-
Copyright (c) 2026 Pavel Grigorenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Pavel Grigorenko
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Complex.Basic

import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.QuadraticDiscriminant


/-!
### Low order roots of unity
TODO
-/

public section

variable {K : Type*} [CommRing K] [IsDomain K]

/-!
#### Quadratic roots of unity
-/

lemma quadratic_roots_of_unity_eq [Invertible (2 : K)] : {z : K | z ^ 2 = 1} = {1, -1} := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro z
  have h := quadratic_eq_zero_iff' (show discrim (1 : K) 0 (-1) = 2 * 2 by rw [discrim]; norm_num) z
  norm_num at h
  conv_lhs at h => rw [← @add_left_cancel_iff _ _ _ (1 : K)]
  conv_rhs at h =>
    congr <;> rhs
    · apply (show ( 2 : K) =  1 * 2 by norm_num)
    · apply (show (-2 : K) = -1 * 2 by norm_num)
  conv_rhs at h => congr <;> rw [mul_left_inj_of_invertible 2]
  ring_nf at h
  exact h

lemma Complex.quadratic_roots_of_unity : {z : ℂ | z ^ 2 = 1} = {1, -1} :=
  quadratic_roots_of_unity_eq

lemma Real.quadratic_roots_of_unity : {z : ℝ | z ^ 2 = 1} = {1, -1} :=
  quadratic_roots_of_unity_eq

lemma quadratic_roots_of_minus_one_of_sq_eq {s : K} (hs : s * s = -1) :
    {z : K | z ^ 2 = -1} = {s, -s} := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro z
  rw [← hs, ← pow_two, sq_eq_sq_iff_eq_or_eq_neg]

omit [IsDomain K] in
lemma quadratic_roots_of_minus_one_of_sq_ne (hs : ¬ IsSquare (-1 : K)) :
    {z : K | z ^ 2 = -1} = ∅ := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
  grind only [IsSquare, pow_two]

lemma Complex.quadratic_roots_of_minus_one : {z : ℂ | z ^ 2 = -1} = {I, -I} :=
  quadratic_roots_of_minus_one_of_sq_eq (by norm_num)

lemma Real.quadratic_roots_of_minus_one : {z : ℝ | z ^ 2 = -1} = ∅ :=
  quadratic_roots_of_minus_one_of_sq_ne (by simp)

/-!
#### Cubic roots of unity
-/

lemma cubic_cyclotomic_polynomial_roots_of_sq [Invertible (2 : K)] {z s : K}
    (hs : s * s = -3) : z ^ 2 + z + 1 = 0 ↔ z = (s - 1) * ⅟2 ∨ z = (-s - 1) * ⅟2 := by
  suffices 1 * (z * z) + 1 * z + 1 = 0 ↔ z = (s - 1) * ⅟2 ∨ z = (-s - 1) * ⅟2 by grind only
  rw [quadratic_eq_zero_iff' (by rw [hs, discrim]; norm_num)]
  iterate 2 rw [← mul_right_eq_iff_eq_mul_invOf]
  ring_nf

omit [IsDomain K] in
lemma cubic_cyclotomic_polynomial_ne_zero_of_sq_ne {z : K} (h : ¬ IsSquare (-3 : K)) :
    z ^ 2 + z + 1 ≠ 0 := by
  suffices 1 * (z * z) + 1 * z + 1 ≠ 0 by
    rwa [one_mul, one_mul, ← sq] at this
  apply quadratic_ne_zero_of_discrim_ne_sq
  grind only [discrim, pow_two, IsSquare]

lemma cubic_roots_of_unity_of_sq_eq [Invertible (2 : K)] {s : K} (hs : s * s = -3) :
    {z : K | z^3 = 1} = {1, (-s - 1) * ⅟2, (s - 1) * ⅟2} := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro z
  simp [show z ^ 3 = (z - 1) * (z ^ 2 + z + 1) + 1 by ring]
  grind only [cubic_cyclotomic_polynomial_roots_of_sq hs,
    quadratic_eq_zero_iff' (show discrim 1 1 1 = s * s by rw [discrim, hs]; norm_num) z]

lemma cubic_roots_of_unity_of_sq_ne (h : ¬ IsSquare (-3 : K)) : {z : K | z^3 = 1} = {1} := by
  rw [Set.eq_singleton_iff_unique_mem, Set.mem_setOf_eq]
  constructor
  · rw [one_pow]
  · intro x
    simp [Set.mem_setOf_eq, show x ^ 3  = (x - 1) * (x ^ 2 + x + 1) + 1 by ring]
    grind only [cubic_cyclotomic_polynomial_ne_zero_of_sq_ne h]

lemma Complex.cubic_roots_of_unity
    : {z : ℂ | z ^ 3 = 1} = {1, -(1 / 2) - √3 / 2 * I, -(1 / 2) + √3 / 2 * I} := by
  have hs : (√3 * I) * (√3 * I) = -3 := by
    ring_nf
    rw [I_sq, ← ofReal_pow, Real.sq_sqrt zero_le_three, mul_neg, mul_one, ofReal_ofNat]
  rw [cubic_roots_of_unity_of_sq_eq hs, show ⅟(2 : ℂ) = 1 / 2 by norm_num]
  ring_nf

lemma Real.cubic_roots_of_unity : {z : ℝ | z ^ 3 = 1} = {1} := by
  rw [cubic_roots_of_unity_of_sq_ne]
  intro h
  apply h.elim
  intro a
  grind only [sq_nonneg a]

/-!
#### Quartic roots of unity
-/

lemma quartic_roots_of_unity_of_sq_eq [Invertible (2 : K)] {s : K} (hs : s * s = -1) :
    {z : K | z ^ 4 = 1} = {1, s, -1, -s} := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have (z : K): z ^ 2 = -1 ↔ z = s ∨ z = -s := by
    have h := quadratic_roots_of_minus_one_of_sq_eq hs
    rw [Set.ext_iff] at h
    apply h
  have (z : K) : z ^ 2 = 1 ↔ z = 1 ∨ z = -1 := by
    have h := @quadratic_roots_of_unity_eq K _
    rw [Set.ext_iff] at h
    apply h
  intro z
  grind [show z ^ 4 = (z ^ 2) ^ 2 by ring]

lemma quartic_roots_of_unity_of_sq_ne (h : ¬ IsSquare (-1 : K)) :
    {z : K | z ^ 4 = 1} = {1, -1} := by
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro z
  simp [show z ^ 4 = (z - 1) * (z + 1) * (z ^ 2 + 1) + 1 by ring_nf]
  grind only [IsSquare, pow_two]

lemma Complex.quartic_roots_of_unity : {z : ℂ | z ^ 4 = 1} = {1, I, -1, -I} :=
  quartic_roots_of_unity_of_sq_eq I_mul_I

lemma Real.quartic_roots_of_unity : {z : ℝ | z ^ 4 = 1} = {1, -1} := by
  rw [quartic_roots_of_unity_of_sq_ne]
  rw [IsSquare, not_exists]
  intro x
  grind only [sq_nonneg x]

/-!
#### Quintic roots of unity
-/

omit [IsDomain K] in
lemma quintic_factorize_cyclotomic_polynomial [Invertible (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) (z : K) :
    z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = (z - ( (s - 1) * ⅟4 + t₁ * ⅟4))
                                  * (z - ( (s - 1) * ⅟4 - t₁ * ⅟4))
                                  * (z - (-(s + 1) * ⅟4 + t₂ * ⅟4))
                                  * (z - (-(s + 1) * ⅟4 - t₂ * ⅟4)) := by
  have s4 : s ^ 4 = 25 := by grind only => ring
  ring_nf
  rw [sq t₁, ht₁, sq t₂, ht₂, sq s, hs, s4]
  ring_nf
  rw [sq s, hs]
  have : ⅟(4 : K) * 4 = 1 := invOf_mul_self _
  grind only

lemma quintic_cyclotomic_polynomial_roots_of_sq [Invertible (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) :
    {z : K | z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0} =
      {(s - 1) * ⅟4 + t₁ * ⅟4,
       (s - 1) * ⅟4 - t₁ * ⅟4,
      -(s + 1) * ⅟4 + t₂ * ⅟4,
      -(s + 1) * ⅟4 - t₂ * ⅟4} := by
  ext
  simp [quintic_factorize_cyclotomic_polynomial hs ht₁ ht₂, sub_eq_zero, or_assoc]

lemma quintic_roots_of_unity_of_sq [Invertible (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) :
  {z : K | z^5 = 1} = {1,
      (s - 1) * ⅟4 + t₁ * ⅟4,
       (s - 1) * ⅟4 - t₁ * ⅟4,
      -(s + 1) * ⅟4 + t₂ * ⅟4,
      -(s + 1) * ⅟4 - t₂ * ⅟4} := by
  rw [← Set.singleton_union, ← quintic_cyclotomic_polynomial_roots_of_sq hs ht₁ ht₂, Set.ext_iff]
  intro z
  rw [Set.mem_setOf_eq,
      show z ^ 5 = 1 ↔ z ^ 5 - 1 = 0 by grind only,
      show z ^ 5 - 1 = (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) * (z - 1) by ring_nf,
      mul_eq_zero]
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  grind only

lemma Complex.quintic_roots_of_unity : {z : ℂ | z ^ 5 = 1} = {1,
    (√5 -1)/4 + √2 * √(5 + √5)/4 * I,
    (√5 -1)/4 - √2 * √(5 + √5)/4 * I,
    -(√5 + 1)/4 + √2 * √(5 - √5) / 4 * I,
    -(√5 +1)/4 - √2 * √(5 - √5) / 4 * I} := by
  have hs : (√5 : ℂ) * √5 = 5 := by
    norm_cast
    norm_num
  have ht₁ : (√2 * √(5 + √5) * I) * (√2 * √(5 + √5) * I) = -2 * (5 + √5) := by
    rw [mul_assoc, mul_comm I,  mul_assoc _ I I, I_mul_I]
    norm_cast
    norm_num
    ring_nf
    rw [Real.sq_sqrt zero_le_two, Real.sq_sqrt (by simp only [Nat.ofNat_nonneg, Real.sqrt_nonneg,
      Left.add_nonneg])]
    ring_nf
  have ht₂ : (√2 * √(5 - √5) * I) * (√2 * √(5 - √5) * I) = -2 * (5 - √5) := by
    rw [mul_assoc, mul_comm I,  mul_assoc _ I I, I_mul_I]
    norm_cast
    norm_num
    ring_nf
    rw [Real.sq_sqrt zero_le_two, Real.sq_sqrt]
    · ring_nf
    · rw [sub_nonneg]
      refine (Real.sqrt_le_left (Nat.ofNat_nonneg' 5)).mpr (by norm_num)
  rw [quintic_roots_of_unity_of_sq hs ht₁ ht₂]
  norm_num
  ring_nf

end
