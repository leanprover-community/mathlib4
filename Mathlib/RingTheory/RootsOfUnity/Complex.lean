/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.

-/


namespace Complex

open Polynomial Real

open scoped Nat Real

theorem isPrimitiveRoot_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := mod_cast h0
  constructor
  · use i
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)]
  · simp only [hn0, Ne, not_false_iff,
      mul_comm _ (i : ℂ), ← mul_assoc _ (i : ℂ), exists_imp, field_simps]
    norm_cast
    rintro l k hk
    conv_rhs at hk => rw [mul_comm, ← mul_assoc]
    have hz : 2 * ↑π * I ≠ 0 := by simp [pi_pos.ne.symm, I_ne_zero]
    field_simp [hz] at hk
    norm_cast at hk
    have : n ∣ i * l := by rw [← Int.natCast_dvd_natCast, hk, mul_comm]; apply dvd_mul_left
    exact hi.symm.dvd_of_dvd_mul_left this

theorem isPrimitiveRoot_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [Nat.cast_one, one_div] using
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

theorem isPrimitiveRoot_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔ ∃ i < n, ∃ _ : i.Coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  field_simp [hn0, mul_comm (i : ℂ)]

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `exp (2 * Real.pi * Complex.I * (i / n))` for some `i < n`. -/
nonrec theorem mem_rootsOfUnity (n : ℕ) [NeZero n] (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, exp (2 * π * I * (i / n)) = x := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  have hn0 : (n : ℂ) ≠ 0 := mod_cast NeZero.out
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x := by
      simpa only using (isPrimitiveRoot_exp n NeZero.out).eq_pow_of_pow_eq_one h
    refine ⟨i, hi, ?_⟩
    rw [← H, ← exp_nat_mul]
    congr 1
    field_simp [hn0, mul_comm (i : ℂ)]
  · rintro ⟨i, _, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)]

theorem card_rootsOfUnity (n : ℕ) [NeZero n] : Fintype.card (rootsOfUnity n ℂ) = n :=
  (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

end Complex

theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖₊ = 1 :=
  Subtype.ext <| h.norm'_eq_one hn

theorem IsPrimitiveRoot.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : IsPrimitiveRoot μ m) (hn : n ≠ 0) (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

theorem IsPrimitiveRoot.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

theorem IsPrimitiveRoot.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

theorem IsPrimitiveRoot.arg {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ∃ i : ℤ, ζ.arg = i / n * (2 * Real.pi) ∧ IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm, ← mul_assoc, Complex.exp_mul_I]
  refine ⟨if i * 2 ≤ n then i else i - n, ?_, ?isCoprime, by omega⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one, sub_eq_add_neg]
  split_ifs with h₂
  · convert Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    field_simp [hn]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      exact mul_nonneg (mul_nonneg i.cast_nonneg <| by simp [Real.pi_pos.le])
        (by rw [inv_nonneg]; simp only [Nat.cast_nonneg])
    rw [← mul_rotate', mul_div_assoc]
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi, ← Complex.sin_sub_two_pi]
  convert Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact mod_cast hn
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact mod_cast hn
  field_simp [hn]
  refine ⟨?_, le_trans ?_ Real.pi_pos.le⟩
  on_goal 2 =>
    rw [mul_div_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr <| mod_cast h.le)
      (div_nonneg (by simp [Real.pi_pos.le]) <| by simp)
  rw [← mul_rotate', mul_div_assoc, neg_lt, ← mul_neg, mul_lt_iff_lt_one_right Real.pi_pos, ←
    neg_div, ← neg_mul, neg_sub, div_lt_iff₀, one_mul, sub_mul, sub_lt_comm, ← mul_sub_one]
  · norm_num
    exact mod_cast not_le.mp h₂
  · exact Nat.cast_pos.mpr hn.bot_lt

lemma Complex.norm_eq_one_of_mem_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n ℂ) :
    ‖(ζ : ℂ)‖ = 1 := by
  refine norm_eq_one_of_pow_eq_one ?_ <| NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ, Units.val_one]

theorem Complex.conj_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n] (hζ : ζ ∈ rootsOfUnity n ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  rw [← Units.mul_eq_one_iff_eq_inv, conj_mul', norm_eq_one_of_mem_rootsOfUnity hζ, ofReal_one,
    one_pow]

/-
Low order roots of unity
-/

section LowOrder

open Complex

variable {K : Type*} [Field K]

/-
Cubic roots of unity
-/

lemma cubic_cyclotomic_polynomial_roots_of_sq [NeZero (2 : K)] {z s : K}
    (hs : s * s = -3) : z ^ 2 + z + 1 = 0 ↔ z = -(1 / 2) + s / 2 ∨ z = -(1 / 2) - s / 2 := by
  suffices 1 * (z * z) + 1 * z + 1 = 0 ↔ z = -(1 / 2) + s / 2 ∨ z = -(1 / 2) - s / 2 by
    rw [← this]; ring_nf
  rw [quadratic_eq_zero_iff one_ne_zero (by rw [hs, discrim]; norm_num)]
  ring_nf

lemma cubic_cyclotomic_polynomial_ne_zero_of_sq_ne {z : K} (h : ∀ s : K, s^2 ≠ -3) :
    z ^ 2 + z + 1 ≠ 0 := by
  suffices 1 * (z * z) + 1 * z + 1 ≠ 0 by
    rw[one_mul, one_mul, ← sq] at this
    exact this
  exact quadratic_ne_zero_of_discrim_ne_sq (fun s => by rw [discrim]; ring_nf; exact (h s).symm) _

lemma cubic_roots_of_unity_of_sq_eq [NeZero (2 : K)] {s : K} (hs : s * s = -3) :
    {z : K | z^3 = 1} = {1, -(1 / 2) + s / 2, -(1 / 2) - s / 2} := by
  have H (z : K) : z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1) := by ring
  ext1 z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← sub_eq_zero, H, ← cubic_cyclotomic_polynomial_roots_of_sq hs, mul_eq_zero, sub_eq_zero]

lemma cubic_roots_of_unity_of_sq_ne (h : ∀ s : K, s^2 ≠ -3) : {z : K | z^3 = 1} = {1} := by
  have H (z : K) : z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1) := by ring
  ext1 z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [← sub_eq_zero, H, mul_eq_zero_iff_right (cubic_cyclotomic_polynomial_ne_zero_of_sq_ne h),
    sub_eq_zero]

example : {z : ℂ | z ^ 3 = 1} = {1, -(1 / 2) + √3 / 2 * I, -(1 / 2) - √3 / 2 * I} := by
  have hs : (√3 * I) * (√3 * I) = -3 := by
    ring_nf
    rw [I_sq, ← ofReal_pow, Real.sq_sqrt zero_le_three, mul_neg, mul_one,  ofReal_ofNat]
  rw [cubic_roots_of_unity_of_sq_eq hs]
  ring_nf

example : {z : ℝ | z ^ 3 = 1} = {1} := by
  rw [cubic_roots_of_unity_of_sq_ne]
  intro s
  by_contra hc
  have e2 : s=0 := by
    rw [← sq_nonpos_iff]
    simp_all only [Left.neg_nonpos_iff, Nat.ofNat_nonneg]
  rw [e2, zero_pow two_ne_zero] at hc
  simp_all only [zero_eq_neg, OfNat.ofNat_ne_zero]

/-
Quartic roots of unity
-/

lemma quartic_roots_of_unity_of_sq_eq {s : K} (hs : s * s = -1) :
    {z : K | z ^ 4 = 1} = {1, s, -1, -s} := by
  have H (z : K) : z ^ 4 - 1 = (z - 1) * (z - s) * (z + 1) * (z + s) := by
    ring_nf
    rw [sq s, hs]
    ring
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← sub_eq_zero, H]
  simp only [← sub_neg_eq_add, mul_eq_zero, sub_eq_zero, or_assoc]

lemma quartic_roots_of_unity_of_sq_ne (h : ∀ s : K, s^2 ≠ -1) : {z : K | z ^ 4 = 1} = {1, -1} := by
  have H (z : K) : z ^ 4 - 1 = (z - 1) * (z + 1) * (z ^ 2 + 1) := by
    ring_nf
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← sub_eq_zero, H]
  rw [mul_eq_zero_iff_right (by
    by_contra hc
    rw [add_eq_zero_iff_eq_neg] at hc
    exact h z hc)]
  rw [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

example : {z : ℂ | z ^ 4 = 1} = {1, I, -1, -I} := quartic_roots_of_unity_of_sq_eq I_mul_I

example : {z : ℝ | z ^ 4 = 1} = {1, -1} := by
  rw [quartic_roots_of_unity_of_sq_ne]
  intro s
  by_contra hc
  have e2 : s=0 := by
    rw [← sq_nonpos_iff, hc]
    simp [Left.neg_nonpos_iff, zero_le_one]
  rw [e2] at hc
  subst e2
  simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_neg, one_ne_zero]

/-
Quintic roots of unity
-/

lemma quintic_factorize_cyclotomic_polynomial [NeZero (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) (z : K) :
    z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = (z - ( (s - 1) / 4 + t₁ / 4))
                                  * (z - ( (s - 1) / 4 - t₁ / 4))
                                  * (z - (-(s + 1) / 4 + t₂ / 4))
                                  * (z - (-(s + 1) / 4 - t₂ / 4)) := by
  have s4 : s ^ 4 = 25 := by
    calc s ^ 4 = (s * s) * (s * s) := by ring_nf
    _ = 5 * 5 := by rw [hs]
    _ = 25 := by norm_num
  ring_nf
  rw [sq t₁, ht₁, sq t₂, ht₂, sq s, hs, s4]
  ring_nf
  rw [sq s, hs]
  ring_nf
  have p2 : (4 : K) ^ 2 = (16 : K) := by norm_num
  have p3 : (4 : K) ^ 3 = (64 : K) := by norm_num
  have p4 : (4 : K) ^ 4 = (256 : K) := by norm_num
  rw [mul_assoc, ← p3, ← mul_pow, mul_assoc, ← p2, ← mul_pow, ← p4, ← mul_pow _ 4, mul_assoc,
    inv_mul_cancel₀ four_ne_zero, one_pow, mul_one, one_pow, mul_one, one_pow]
  ring_nf

lemma quintic_cyclotomic_polynomial_roots_of_sq [NeZero (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) :
    {z : K | z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0} =
      {(s - 1) / 4 + t₁ / 4,
       (s - 1) / 4 - t₁ / 4,
      -(s + 1) / 4 + t₂ / 4,
      -(s + 1) / 4 - t₂ / 4} := by
  ext1 z
  simp only [(quintic_factorize_cyclotomic_polynomial hs ht₁ ht₂), neg_add_rev, mul_eq_zero,
    sub_eq_zero, or_assoc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

lemma quintic_roots_of_unity_of_sq [NeZero (4 : K)] {s t₁ t₂ : K} (hs : s * s = 5)
    (ht₁ : t₁ * t₁ = -2 * (5 + s)) (ht₂ : t₂ * t₂ = -2 * (5 - s)) :
  {z : K | z^5 = 1} = {1,
      (s - 1) / 4 + t₁ / 4,
       (s - 1) / 4 - t₁ / 4,
      -(s + 1) / 4 + t₂ / 4,
      -(s + 1) / 4 - t₂ / 4} := by
  have H (z : K) : z ^ 5 - 1 = (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) := by ring
  rw [← Set.singleton_union, ← quintic_cyclotomic_polynomial_roots_of_sq hs ht₁ ht₂]
  ext1 z
  simp only [Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff]
  rw [← sub_eq_zero, H, mul_eq_zero, sub_eq_zero]

example : {z : ℂ | z ^ 5 = 1} = {1,
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
    ring_nf
    rw [sub_nonneg]
    refine (Real.sqrt_le_left (Nat.ofNat_nonneg' 5)).mpr (by norm_num)
  rw [quintic_roots_of_unity_of_sq hs ht₁ ht₂]
  ring_nf

end LowOrder
