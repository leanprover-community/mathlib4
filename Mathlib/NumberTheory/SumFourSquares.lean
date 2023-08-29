/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Data.Fintype.BigOperators

#align_import number_theory.sum_four_squares from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/


open Finset Polynomial FiniteField Equiv

open scoped BigOperators

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- **Euler's four-square identity**. -/
theorem euler_four_squares {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
                                                                              -- 🎉 no goals

/-- **Euler's four-square identity**, a version for natural numbers. -/
theorem Nat.euler_four_squares (a b c d x y z w : ℕ) :
    ((a : ℤ) * x - b * y - c * z - d * w).natAbs ^ 2 +
      ((a : ℤ) * y + b * x + c * w - d * z).natAbs ^ 2 +
      ((a : ℤ) * z - b * w + c * x + d * y).natAbs ^ 2 +
      ((a : ℤ) * w + b * z - c * y + d * x).natAbs ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  rw [← Int.coe_nat_inj']
  -- ⊢ ↑(Int.natAbs (↑a * ↑x - ↑b * ↑y - ↑c * ↑z - ↑d * ↑w) ^ 2 + Int.natAbs (↑a *  …
  push_cast
  -- ⊢ |↑a * ↑x - ↑b * ↑y - ↑c * ↑z - ↑d * ↑w| ^ 2 + |↑a * ↑y + ↑b * ↑x + ↑c * ↑w - …
  simp only [sq_abs, _root_.euler_four_squares]
  -- 🎉 no goals

namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : 2 * m = x ^ 2 + y ^ 2) :
    m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
  have : Even (x ^ 2 + y ^ 2) := by simp [← h, even_mul]
                                    -- 🎉 no goals
  have hxaddy : Even (x + y) := by simpa [sq, parity_simps]
                                   -- 🎉 no goals
  have hxsuby : Even (x - y) := by simpa [sq, parity_simps]
                                   -- 🎉 no goals
  mul_right_injective₀ (show (2 * 2 : ℤ) ≠ 0 by decide) <|
                                                -- 🎉 no goals
    calc
      2 * 2 * m = (x - y) ^ 2 + (x + y) ^ 2 := by rw [mul_assoc, h]; ring
                                                  -- ⊢ ↑2 * (x ^ 2 + y ^ 2) = (x - y) ^ 2 + (x + y) ^ 2
                                                                     -- 🎉 no goals
      _ = (2 * ((x - y) / 2)) ^ 2 + (2 * ((x + y) / 2)) ^ 2 := by
        rw [even_iff_two_dvd] at hxsuby hxaddy
        -- ⊢ (x - y) ^ 2 + (x + y) ^ 2 = (2 * ((x - y) / 2)) ^ 2 + (2 * ((x + y) / 2)) ^ 2
        rw [Int.mul_ediv_cancel' hxsuby, Int.mul_ediv_cancel' hxaddy]
        -- 🎉 no goals
      _ = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) := by
        simp [mul_add, pow_succ, mul_comm, mul_assoc, mul_left_comm]
        -- 🎉 no goals
#align int.sq_add_sq_of_two_mul_sq_add_sq Int.sq_add_sq_of_two_mul_sq_add_sq

-- porting note: new theorem
theorem lt_of_sum_four_squares_eq_mul {a b c d k m : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k * m)
    (ha : 2 * a < m) (hb : 2 * b < m) (hc : 2 * c < m) (hd : 2 * d < m) :
    k < m := by
  refine lt_of_mul_lt_mul_right (lt_of_mul_lt_mul_left ?_ (zero_le (2 ^ 2))) (zero_le m)
  -- ⊢ 2 ^ 2 * (k * m) < 2 ^ 2 * (m * m)
  calc
    2 ^ 2 * (k * ↑m) = ∑ i : Fin 4, (2 * ![a, b, c, d] i) ^ 2 := by
      simp [← h, Fin.sum_univ_succ, mul_add, mul_pow, add_assoc]
    _ < ∑ _i : Fin 4, m ^ 2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ by
      refine pow_lt_pow_of_lt_left ?_ (zero_le _) two_pos
      fin_cases i <;> assumption
    _ = 2 ^ 2 * (m * m) := by simp; ring

-- porting note: new theorem
theorem exists_sq_add_sq_add_one_eq_mul (p : ℕ) [hp : Fact p.Prime] :
    ∃ (a b k : ℕ), 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p := by
  rcases hp.1.eq_two_or_odd' with (rfl | hodd)
  -- ⊢ ∃ a b k, 0 < k ∧ k < 2 ∧ a ^ 2 + b ^ 2 + 1 = k * 2
  · use 1, 0, 1; simp
    -- ⊢ 0 < 1 ∧ 1 < 2 ∧ 1 ^ 2 + 0 ^ 2 + 1 = 1 * 2
                 -- 🎉 no goals
  rcases Nat.sq_add_sq_zmodEq p (-1) with ⟨a, b, ha, hb, hab⟩
  -- ⊢ ∃ a b k, 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p
  rcases Int.modEq_iff_dvd.1 hab.symm with ⟨k, hk⟩
  -- ⊢ ∃ a b k, 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p
  rw [sub_neg_eq_add, mul_comm] at hk
  -- ⊢ ∃ a b k, 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p
  have hk₀ : 0 < k
  -- ⊢ 0 < k
  · refine pos_of_mul_pos_left ?_ (Nat.cast_nonneg p)
    -- ⊢ 0 < k * ↑p
    rw [← hk]
    -- ⊢ 0 < ↑a ^ 2 + ↑b ^ 2 + 1
    positivity
    -- 🎉 no goals
  lift k to ℕ using hk₀.le
  -- ⊢ ∃ a b k, 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p
  refine ⟨a, b, k, Nat.cast_pos.1 hk₀, ?_, by exact_mod_cast hk⟩
  -- ⊢ k < p
  replace hk : a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = k * p
  -- ⊢ a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = k * p
  · exact_mod_cast hk
    -- 🎉 no goals
  refine lt_of_sum_four_squares_eq_mul hk ?_ ?_ ?_ ?_
  · exact (mul_le_mul' le_rfl ha).trans_lt (Nat.mul_div_lt_iff_not_dvd.2 hodd.not_two_dvd_nat)
    -- 🎉 no goals
  · exact (mul_le_mul' le_rfl hb).trans_lt (Nat.mul_div_lt_iff_not_dvd.2 hodd.not_two_dvd_nat)
    -- 🎉 no goals
  · exact lt_of_le_of_ne hp.1.two_le (hodd.ne_two_of_dvd_nat (dvd_refl _)).symm
    -- 🎉 no goals
  · exact hp.1.pos
    -- 🎉 no goals

@[deprecated exists_sq_add_sq_add_one_eq_mul]
theorem exists_sq_add_sq_add_one_eq_k (p : ℕ) [Fact p.Prime] :
    ∃ (a b : ℤ) (k : ℕ), a ^ 2 + b ^ 2 + 1 = k * p ∧ k < p :=
  let ⟨a, b, k, _, hkp, hk⟩ := exists_sq_add_sq_add_one_eq_mul p
  ⟨a, b, k, by exact_mod_cast hk, hkp⟩
               -- 🎉 no goals
#align int.exists_sq_add_sq_add_one_eq_k Int.exists_sq_add_sq_add_one_eq_k

end Int

namespace Nat

open Int

open scoped Classical

private theorem sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) :
    ∃ w x y z : ℤ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have : ∀ f : Fin 4 → ZMod 2, f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2 = 0 → ∃ i : Fin 4,
      f i ^ 2 + f (swap i 0 1) ^ 2 = 0 ∧ f (swap i 0 2) ^ 2 + f (swap i 0 3) ^ 2 = 0 := by
    decide
  set f : Fin 4 → ℤ := ![a, b, c, d]
  -- ⊢ ∃ w x y z, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m
  obtain ⟨i, hσ⟩ := this (fun x => ↑(f x)) <| by
    rw [← @zero_mul (ZMod 2) _ m, ← show ((2 : ℤ) : ZMod 2) = 0 from rfl, ← Int.cast_mul, ← h]
    simp only [Int.cast_add, Int.cast_pow]
    rfl
  set σ := swap i 0
  -- ⊢ ∃ w x y z, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m
  obtain ⟨x, hx⟩ : (2 : ℤ) ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2 :=
    (CharP.int_cast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [Int.cast_pow, Int.cast_add, Equiv.swap_apply_right, ZMod.pow_card] using hσ.1
  obtain ⟨y, hy⟩ : (2 : ℤ) ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2 :=
    (CharP.int_cast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [Int.cast_pow, Int.cast_add, ZMod.pow_card] using hσ.2
  refine ⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2,
    (f (σ 2) + f (σ 3)) / 2, ?_⟩
  rw [← Int.sq_add_sq_of_two_mul_sq_add_sq hx.symm, add_assoc,
    ← Int.sq_add_sq_of_two_mul_sq_add_sq hy.symm, ← mul_right_inj' two_ne_zero, ← h, mul_add]
  have : (∑ x, f (σ x) ^ 2) = ∑ x, f x ^ 2 := Equiv.sum_comp σ (f · ^ 2)
  -- ⊢ 2 * x + 2 * y = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
  simpa only [← hx, ← hy, Fin.sum_univ_four, add_assoc] using this
  -- 🎉 no goals

/-- Lagrange's **four squares theorem** for a prime number. Use `Nat.sum_four_squares` instead. -/
protected theorem Prime.sum_four_squares {p : ℕ} (hp : p.Prime) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p := by
  have := Fact.mk hp
  -- ⊢ ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p
  -- Find `a`, `b`, `c`, `d`, `0 < m < p` such that `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p`
  have natAbs_iff {a b c d : ℤ} {k : ℕ} :
      a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = k ↔
        a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k := by
    rw [← @Nat.cast_inj ℤ]; push_cast [sq_abs]; rfl
  have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p
  -- ⊢ ∃ m, m < p ∧ 0 < m ∧ ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p
  · obtain ⟨a, b, k, hk₀, hkp, hk⟩ := exists_sq_add_sq_add_one_eq_mul p
    -- ⊢ ∃ m, m < p ∧ 0 < m ∧ ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p
    refine ⟨k, hkp, hk₀, a, b, 1, 0, ?_⟩
    -- ⊢ a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = k * p
    simpa
    -- 🎉 no goals
  -- Take the minimal possible `m`
  rcases Nat.findX hm with ⟨m, ⟨hmp, hm₀, a, b, c, d, habcd⟩, hmin⟩
  -- ⊢ ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p
  -- If `m = 1`, then we are done
  rcases (Nat.one_le_iff_ne_zero.2 hm₀.ne').eq_or_gt with rfl | hm₁
  -- ⊢ ∃ a b c d, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p
  · use a, b, c, d; simpa using habcd
    -- ⊢ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p
                    -- 🎉 no goals
  -- Otherwise, let us find a contradiction
  exfalso
  -- ⊢ False
  have : NeZero m := ⟨hm₀.ne'⟩
  -- ⊢ False
  by_cases hm : 2 ∣ m
  -- ⊢ False
  · -- If `m` is an even number, then `(m / 2) * p` can be represented as a sum of four squares
    rcases hm with ⟨m, rfl⟩
    -- ⊢ False
    rw [zero_lt_mul_left two_pos] at hm₀
    -- ⊢ False
    have hm₂ : m < 2 * m := by simpa [two_mul]
    -- ⊢ False
    apply_fun (Nat.cast : ℕ → ℤ) at habcd
    -- ⊢ False
    push_cast [mul_assoc] at habcd
    -- ⊢ False
    obtain ⟨_, _, _, _, h⟩ := sum_four_squares_of_two_mul_sum_four_squares habcd
    -- ⊢ False
    exact hmin m hm₂ ⟨hm₂.trans hmp, hm₀, _, _, _, _, natAbs_iff.2 h⟩
    -- 🎉 no goals
  · -- For each `x` in `a`, `b`, `c`, `d`, take a number `f x ≡ x [ZMOD m]` with least possible
    -- absolute value
    obtain ⟨f, hf_lt, hf_mod⟩ : ∃ f : ℕ → ℤ, (∀ x, 2 * (f x).natAbs < m) ∧ ∀ x, (f x : ZMod m) = x
    -- ⊢ ∃ f, (∀ (x : ℕ), 2 * natAbs (f x) < m) ∧ ∀ (x : ℕ), ↑(f x) = ↑x
    · refine ⟨fun x ↦ (x : ZMod m).valMinAbs, fun x ↦ ?_, fun x ↦ (x : ZMod m).coe_valMinAbs⟩
      -- ⊢ 2 * natAbs ((fun x => ZMod.valMinAbs ↑x) x) < m
      exact (mul_le_mul' le_rfl (x : ZMod m).natAbs_valMinAbs_le).trans_lt
        (Nat.mul_div_lt_iff_not_dvd.2 hm)
    -- Since `|f x| ^ 2 = (f x) ^ 2 ≡ x ^ 2 [ZMOD m]`, we have
    -- `m ∣ |f a| ^ 2 + |f b| ^ 2 + |f c| ^ 2 + |f d| ^ 2`
    obtain ⟨r, hr⟩ : m ∣ (f a).natAbs ^ 2 + (f b).natAbs ^ 2 + (f c).natAbs ^ 2 + (f d).natAbs ^ 2
    -- ⊢ m ∣ natAbs (f a) ^ 2 + natAbs (f b) ^ 2 + natAbs (f c) ^ 2 + natAbs (f d) ^ 2
    · simp only [← Int.coe_nat_dvd, ← ZMod.int_cast_zmod_eq_zero_iff_dvd]
      -- ⊢ ↑↑(natAbs (f a) ^ 2 + natAbs (f b) ^ 2 + natAbs (f c) ^ 2 + natAbs (f d) ^ 2 …
      push_cast [hf_mod, sq_abs]
      -- ⊢ ↑a ^ 2 + ↑b ^ 2 + ↑c ^ 2 + ↑d ^ 2 = 0
      norm_cast
      -- ⊢ ↑(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 0
      simp [habcd]
      -- 🎉 no goals
    -- The quotient `r` is not zero, because otherwise `f a = f b = f c = f d = 0`, hence
    -- `m` divides each `a`, `b`, `c`, `d`, thus `m ∣ p` which is impossible.
    rcases (zero_le r).eq_or_gt with rfl | hr₀
    -- ⊢ False
    · replace hr : f a = 0 ∧ f b = 0 ∧ f c = 0 ∧ f d = 0; · simpa [and_assoc] using hr
      -- ⊢ f a = 0 ∧ f b = 0 ∧ f c = 0 ∧ f d = 0
                                                            -- 🎉 no goals
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ : m ∣ a ∧ m ∣ b ∧ m ∣ c ∧ m ∣ d
      -- ⊢ m ∣ a ∧ m ∣ b ∧ m ∣ c ∧ m ∣ d
      · simp only [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, ← hf_mod, hr, Int.cast_zero]
        -- 🎉 no goals
      have : m * m ∣ m * p := habcd ▸ ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, by ring⟩
      -- ⊢ False
      rw [mul_dvd_mul_iff_left hm₀.ne'] at this
      -- ⊢ False
      exact (hp.eq_one_or_self_of_dvd _ this).elim hm₁.ne' hmp.ne
      -- 🎉 no goals
    -- Since `2 * |f x| < m` for each `x ∈ {a, b, c, d}`, we have `r < m`
    have hrm : r < m
    -- ⊢ r < m
    · rw [mul_comm] at hr
      -- ⊢ r < m
      apply lt_of_sum_four_squares_eq_mul hr <;> apply hf_lt
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
    -- Now it suffices to represent `r * p` as a sum of four squares
    -- More precisely, we will represent `(m * r) * (m * p)` as a sum of squares of four numbers,
    -- each of them is divisible by `m`
    rsuffices ⟨w, x, y, z, hw, hx, hy, hz, h⟩ : ∃ w x y z : ℤ, ↑m ∣ w ∧ ↑m ∣ x ∧ ↑m ∣ y ∧ ↑m ∣ z ∧
      w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = ↑(m * r) * ↑(m * p)
    · have : (w / m) ^ 2 + (x / m) ^ 2 + (y / m) ^ 2 + (z / m) ^ 2 = ↑(r * p)
      -- ⊢ (w / ↑m) ^ 2 + (x / ↑m) ^ 2 + (y / ↑m) ^ 2 + (z / ↑m) ^ 2 = ↑(r * p)
      · refine mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.2 hm₀.ne')) ?_
        -- ⊢ ↑m ^ 2 * ((w / ↑m) ^ 2 + (x / ↑m) ^ 2 + (y / ↑m) ^ 2 + (z / ↑m) ^ 2) = ↑m ^  …
        conv_rhs => rw [← Nat.cast_pow, ← Nat.cast_mul, sq m, mul_mul_mul_comm, Nat.cast_mul, ← h]
        -- ⊢ ↑m ^ 2 * ((w / ↑m) ^ 2 + (x / ↑m) ^ 2 + (y / ↑m) ^ 2 + (z / ↑m) ^ 2) = w ^ 2 …
        simp only [mul_add, ← mul_pow, Int.mul_ediv_cancel', *]
        -- 🎉 no goals
      rw [← natAbs_iff] at this
      -- ⊢ False
      exact hmin r hrm ⟨hrm.trans hmp, hr₀, _, _, _, _, this⟩
      -- 🎉 no goals
    -- To do the last step, we apply the Euler's four square identity once more
    replace hr : (f b) ^ 2 + (f a) ^ 2 + (f d) ^ 2 + (-f c) ^ 2 = ↑(m * r)
    -- ⊢ f b ^ 2 + f a ^ 2 + f d ^ 2 + (-f c) ^ 2 = ↑(m * r)
    · rw [← natAbs_iff, natAbs_neg, ← hr]
      -- ⊢ natAbs (f b) ^ 2 + natAbs (f a) ^ 2 + natAbs (f d) ^ 2 + natAbs (f c) ^ 2 =  …
      ac_rfl
      -- 🎉 no goals
    have := congr_arg₂ (· * Nat.cast ·) hr habcd
    -- ⊢ ∃ w x y z, ↑m ∣ w ∧ ↑m ∣ x ∧ ↑m ∣ y ∧ ↑m ∣ z ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 …
    simp only [← _root_.euler_four_squares, Nat.cast_add, Nat.cast_pow] at this
    -- ⊢ ∃ w x y z, ↑m ∣ w ∧ ↑m ∣ x ∧ ↑m ∣ y ∧ ↑m ∣ z ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 …
    refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, this⟩
    · simp [← ZMod.int_cast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]
      -- 🎉 no goals
    · suffices : ((a : ZMod m) ^ 2 + (b : ZMod m) ^ 2 + (c : ZMod m) ^ 2 + (d : ZMod m) ^ 2) = 0
      -- ⊢ ↑m ∣ f b * ↑b + f a * ↑a + f d * ↑d - -f c * ↑c
      · simpa [← ZMod.int_cast_zmod_eq_zero_iff_dvd, hf_mod, sq, add_comm, add_assoc,
          add_left_comm] using this
      norm_cast
      -- ⊢ ↑(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 0
      simp [habcd]
      -- 🎉 no goals
    · simp [← ZMod.int_cast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]
      -- 🎉 no goals
    · simp [← ZMod.int_cast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]
      -- 🎉 no goals

/-- **Four squares theorem** -/
theorem sum_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  -- The proof is by induction on prime factorization. The case of prime `n` was proved above,
  -- the inductive step follows from `Nat.euler_four_squares`.
  induction n using Nat.recOnMul with
  | h0 => exact ⟨0, 0, 0, 0, rfl⟩
  | h1 => exact ⟨1, 0, 0, 0, rfl⟩
  | hp p hp => exact hp.sum_four_squares
  | h m n hm hn =>
    rcases hm with ⟨a, b, c, d, rfl⟩
    rcases hn with ⟨w, x, y, z, rfl⟩
    exact ⟨_, _, _, _, euler_four_squares _ _ _ _ _ _ _ _⟩

#align nat.sum_four_squares Nat.sum_four_squares

end Nat
