/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Rify

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
    simp [field, mul_comm (i : ℂ), mul_comm (n : ℂ)]
  · simp only [forall_exists_index]
    rintro l k hk
    have hz : π ≠ 0 := pi_pos.ne'
    field_simp [hz, I_ne_zero] at hk
    norm_cast at hk
    have : n ∣ l * i := by rw [← Int.natCast_dvd_natCast, hk]; apply dvd_mul_right
    exact hi.symm.dvd_of_dvd_mul_right this

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
  field_simp

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
    field_simp
  · rintro ⟨i, _, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    simp [field]

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
    simp
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      positivity
    refine Eq.trans_le (b := Real.pi * (i * 2 / n)) (by ring) ?_
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
  simp
  field_simp
  constructor
  · push_neg at h₂
    rify at h₂
    rw [lt_div_iff₀ (by positivity)]
    linear_combination Real.pi * h₂
  · rify at h
    rw [div_le_iff₀ (by positivity)]
    linear_combination 2 * Real.pi * h + (n:ℝ) * Real.pi_pos

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
