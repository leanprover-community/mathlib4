/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import ring_theory.roots_of_unity.complex from "leanprover-community/mathlib"@"7fdeecc0d03cd40f7a165e6cf00a4d2286db599f"

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.

-/


namespace Complex

open Polynomial Real

open scoped Nat Real

theorem isPrimitiveRoot_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  -- ⊢ exp (2 * ↑π * I * (↑i / ↑n)) ^ n = 1 ∧ ∀ (l : ℕ), exp (2 * ↑π * I * (↑i / ↑n …
  simp only [← exp_nat_mul, exp_eq_one_iff]
  -- ⊢ (∃ n_1, ↑n * (2 * ↑π * I * (↑i / ↑n)) = ↑n_1 * (2 * ↑π * I)) ∧ ∀ (l : ℕ), (∃ …
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast h0
  -- ⊢ (∃ n_1, ↑n * (2 * ↑π * I * (↑i / ↑n)) = ↑n_1 * (2 * ↑π * I)) ∧ ∀ (l : ℕ), (∃ …
  constructor
  -- ⊢ ∃ n_1, ↑n * (2 * ↑π * I * (↑i / ↑n)) = ↑n_1 * (2 * ↑π * I)
  · use i
    -- ⊢ ↑n * (2 * ↑π * I * (↑i / ↑n)) = ↑↑i * (2 * ↑π * I)
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)]
    -- 🎉 no goals
  · simp only [hn0, mul_right_comm _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, Ne.def, not_false_iff,
      mul_comm _ (i : ℂ), ← mul_assoc _ (i : ℂ), exists_imp, field_simps]
    norm_cast
    -- ⊢ ∀ (l : ℕ) (x : ℤ), ↑(i * l) * (↑(2 * π) * I) = ↑x * (↑(2 * π) * I) * ↑n → n  …
    rintro l k hk
    -- ⊢ n ∣ l
    conv_rhs at hk => rw [mul_comm, ← mul_assoc]
    -- ⊢ n ∣ l
    have hz : 2 * ↑π * I ≠ 0 := by simp [pi_pos.ne.symm, I_ne_zero]
    -- ⊢ n ∣ l
    field_simp [hz] at hk
    -- ⊢ n ∣ l
    norm_cast at hk
    -- ⊢ n ∣ l
    have : n ∣ i * l := by rw [← Int.coe_nat_dvd, hk, mul_comm]; apply dvd_mul_left
    -- ⊢ n ∣ l
    exact hi.symm.dvd_of_dvd_mul_left this
    -- 🎉 no goals
#align complex.is_primitive_root_exp_of_coprime Complex.isPrimitiveRoot_exp_of_coprime

theorem isPrimitiveRoot_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [Nat.cast_one, one_div] using
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left
#align complex.is_primitive_root_exp Complex.isPrimitiveRoot_exp

theorem isPrimitiveRoot_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔ ∃ i < (n : ℕ), ∃ _ : i.coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  -- ⊢ IsPrimitiveRoot ζ n ↔ ∃ i, i < n ∧ ∃ x, exp (2 * ↑π * I * (↑i / ↑n)) = ζ
  constructor; swap
  -- ⊢ IsPrimitiveRoot ζ n → ∃ i, i < n ∧ ∃ x, exp (2 * ↑π * I * (↑i / ↑n)) = ζ
               -- ⊢ (∃ i, i < n ∧ ∃ x, exp (2 * ↑π * I * (↑i / ↑n)) = ζ) → IsPrimitiveRoot ζ n
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
    -- ⊢ IsPrimitiveRoot (exp (2 * ↑π * I * (↑i / ↑n))) n
                            -- 🎉 no goals
  intro h
  -- ⊢ ∃ i, i < n ∧ ∃ x, exp (2 * ↑π * I * (↑i / ↑n)) = ζ
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (Nat.pos_of_ne_zero hn)
  refine' ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, _⟩
  -- ⊢ exp (2 * ↑π * I * (↑i / ↑n)) = exp (2 * ↑π * I / ↑n) ^ i
  rw [← exp_nat_mul]
  -- ⊢ exp (2 * ↑π * I * (↑i / ↑n)) = exp (↑i * (2 * ↑π * I / ↑n))
  congr 1
  -- ⊢ 2 * ↑π * I * (↑i / ↑n) = ↑i * (2 * ↑π * I / ↑n)
  field_simp [hn0, mul_comm (i : ℂ)]
  -- 🎉 no goals
#align complex.is_primitive_root_iff Complex.isPrimitiveRoot_iff

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `exp (2 * Real.pi * Complex.I * (i / n))` for some `i < n`. -/
nonrec theorem mem_rootsOfUnity (n : ℕ+) (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < (n : ℕ), exp (2 * π * I * (i / n)) = x := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  -- ⊢ ↑x ^ ↑n = 1 ↔ ∃ i, i < ↑n ∧ exp (2 * ↑π * I * (↑i / ↑↑n)) = ↑x
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  -- ⊢ ↑x ^ ↑n = 1 ↔ ∃ i, i < ↑n ∧ exp (2 * ↑π * I * (↑i / ↑↑n)) = ↑x
  constructor
  -- ⊢ ↑x ^ ↑n = 1 → ∃ i, i < ↑n ∧ exp (2 * ↑π * I * (↑i / ↑↑n)) = ↑x
  · intro h
    -- ⊢ ∃ i, i < ↑n ∧ exp (2 * ↑π * I * (↑i / ↑↑n)) = ↑x
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x := by
      simpa only using (isPrimitiveRoot_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos
    refine' ⟨i, hi, _⟩
    -- ⊢ exp (2 * ↑π * I * (↑i / ↑↑n)) = ↑x
    rw [← H, ← exp_nat_mul]
    -- ⊢ exp (2 * ↑π * I * (↑i / ↑↑n)) = exp (↑i * (2 * ↑π * I / ↑↑n))
    congr 1
    -- ⊢ 2 * ↑π * I * (↑i / ↑↑n) = ↑i * (2 * ↑π * I / ↑↑n)
    field_simp [hn0, mul_comm (i : ℂ)]
    -- 🎉 no goals
  · rintro ⟨i, _, H⟩
    -- ⊢ ↑x ^ ↑n = 1
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    -- ⊢ ∃ n_1, ↑↑n * (2 * ↑π * I * (↑i / ↑↑n)) = ↑n_1 * (2 * ↑π * I)
    use i
    -- ⊢ ↑↑n * (2 * ↑π * I * (↑i / ↑↑n)) = ↑↑i * (2 * ↑π * I)
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)]
    -- 🎉 no goals
#align complex.mem_roots_of_unity Complex.mem_rootsOfUnity

theorem card_rootsOfUnity (n : ℕ+) : Fintype.card (rootsOfUnity n ℂ) = n :=
  (isPrimitiveRoot_exp n n.ne_zero).card_rootsOfUnity
#align complex.card_roots_of_unity Complex.card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases h : k = 0
  -- ⊢ Finset.card (primitiveRoots k ℂ) = φ k
  · simp [h]
    -- 🎉 no goals
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots
  -- 🎉 no goals
#align complex.card_primitive_roots Complex.card_primitiveRoots

end Complex

theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn
#align is_primitive_root.norm'_eq_one IsPrimitiveRoot.norm'_eq_one

theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖₊ = 1 :=
  Subtype.ext <| h.norm'_eq_one hn
#align is_primitive_root.nnnorm_eq_one IsPrimitiveRoot.nnnorm_eq_one

theorem IsPrimitiveRoot.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : IsPrimitiveRoot μ m) (hn : n ≠ 0) (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_abs_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h
#align is_primitive_root.arg_ext IsPrimitiveRoot.arg_ext

theorem IsPrimitiveRoot.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩
#align is_primitive_root.arg_eq_zero_iff IsPrimitiveRoot.arg_eq_zero_iff

theorem IsPrimitiveRoot.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩
#align is_primitive_root.arg_eq_pi_iff IsPrimitiveRoot.arg_eq_pi_iff

theorem IsPrimitiveRoot.arg {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ∃ i : ℤ, ζ.arg = i / n * (2 * Real.pi) ∧ IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  -- ⊢ ∃ i, Complex.arg ζ = ↑i / ↑n * (2 * Real.pi) ∧ IsCoprime i ↑n ∧ Int.natAbs i …
  obtain ⟨i, h, hin, rfl⟩ := h
  -- ⊢ ∃ i_1, Complex.arg (Complex.exp (2 * ↑Real.pi * Complex.I * (↑i / ↑n))) = ↑i …
  rw [mul_comm, ← mul_assoc, Complex.exp_mul_I]
  -- ⊢ ∃ i_1, Complex.arg (Complex.cos (↑i / ↑n * (2 * ↑Real.pi)) + Complex.sin (↑i …
  refine' ⟨if i * 2 ≤ n then i else i - n, _, _, _⟩
  on_goal 2 =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one, sub_eq_add_neg]
  on_goal 2 =>
    split_ifs with h₂
    · exact_mod_cast h
    suffices (i - n : ℤ).natAbs = n - i by
      rw [this]
      apply tsub_lt_self hn.bot_lt
      contrapose! h₂
      rw [Nat.eq_zero_of_le_zero h₂, zero_mul]
      exact zero_le _
    rw [← Int.natAbs_neg, neg_sub, Int.natAbs_eq_iff]
    exact Or.inl (Int.ofNat_sub h.le).symm
  split_ifs with h₂
  -- ⊢ Complex.arg (Complex.cos (↑i / ↑n * (2 * ↑Real.pi)) + Complex.sin (↑i / ↑n * …
  · convert Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
      -- ⊢ ↑i / ↑n * (2 * ↑Real.pi) = ↑i / ↑n * (2 * ↑Real.pi)
                 -- 🎉 no goals
    · push_cast; rfl
      -- ⊢ ↑i / ↑n * (2 * ↑Real.pi) = ↑i / ↑n * (2 * ↑Real.pi)
                 -- 🎉 no goals
    field_simp [hn]
    -- ⊢ -Real.pi < ↑i * (2 * Real.pi) / ↑n ∧ ↑i * (2 * Real.pi) / ↑n ≤ Real.pi
    refine' ⟨(neg_lt_neg Real.pi_pos).trans_le _, _⟩
    -- ⊢ -0 ≤ ↑i * (2 * Real.pi) / ↑n
    · rw [neg_zero]
      -- ⊢ 0 ≤ ↑i * (2 * Real.pi) / ↑n
      exact mul_nonneg (mul_nonneg i.cast_nonneg <| by simp [Real.pi_pos.le])
        (by rw [inv_nonneg]; simp only [Nat.cast_nonneg])
    rw [← mul_rotate', mul_div_assoc]
    -- ⊢ Real.pi * (↑i * 2 / ↑n) ≤ Real.pi
    rw [← mul_one n] at h₂
    -- ⊢ Real.pi * (↑i * 2 / ↑n) ≤ Real.pi
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff' <| by exact_mod_cast pos_of_gt h).mpr <| by exact_mod_cast h₂)
  rw [← Complex.cos_sub_two_pi, ← Complex.sin_sub_two_pi]
  -- ⊢ Complex.arg (Complex.cos (↑i / ↑n * (2 * ↑Real.pi) - 2 * ↑Real.pi) + Complex …
  convert Complex.arg_cos_add_sin_mul_I _
  · push_cast
    -- ⊢ ↑i / ↑n * (2 * ↑Real.pi) - 2 * ↑Real.pi = (↑i - ↑n) / ↑n * (2 * ↑Real.pi)
    rw [← sub_one_mul, sub_div, div_self]
    -- ⊢ ↑n ≠ 0
    exact_mod_cast hn
    -- 🎉 no goals
  · push_cast
    -- ⊢ ↑i / ↑n * (2 * ↑Real.pi) - 2 * ↑Real.pi = (↑i - ↑n) / ↑n * (2 * ↑Real.pi)
    rw [← sub_one_mul, sub_div, div_self]
    -- ⊢ ↑n ≠ 0
    exact_mod_cast hn
    -- 🎉 no goals
  field_simp [hn]
  -- ⊢ -Real.pi < (↑i - ↑n) * (2 * Real.pi) / ↑n ∧ (↑i - ↑n) * (2 * Real.pi) / ↑n ≤ …
  refine' ⟨_, le_trans _ Real.pi_pos.le⟩
  -- ⊢ -Real.pi < (↑i - ↑n) * (2 * Real.pi) / ↑n
  on_goal 2 =>
    rw [mul_div_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr <| by exact_mod_cast h.le)
      (div_nonneg (by simp [Real.pi_pos.le]) <| by simp)
  rw [← mul_rotate', mul_div_assoc, neg_lt, ← mul_neg, mul_lt_iff_lt_one_right Real.pi_pos, ←
    neg_div, ← neg_mul, neg_sub, div_lt_iff, one_mul, sub_mul, sub_lt_comm, ← mul_sub_one]
  norm_num
  -- ⊢ ↑n < ↑i * 2
  exact_mod_cast not_le.mp h₂
  -- ⊢ 0 < ↑n
  · exact Nat.cast_pos.mpr hn.bot_lt
    -- 🎉 no goals
#align is_primitive_root.arg IsPrimitiveRoot.arg
