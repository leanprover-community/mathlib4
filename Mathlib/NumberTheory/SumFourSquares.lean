/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/

public section


open Finset Polynomial FiniteField Equiv

/-- **Euler's four-square identity**. -/
theorem euler_four_squares {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring

/-- **Euler's four-square identity**, a version for natural numbers. -/
theorem Nat.euler_four_squares (a b c d x y z w : ℕ) :
    ((a : ℤ) * x - b * y - c * z - d * w).natAbs ^ 2 +
      ((a : ℤ) * y + b * x + c * w - d * z).natAbs ^ 2 +
      ((a : ℤ) * z - b * w + c * x + d * y).natAbs ^ 2 +
      ((a : ℤ) * w + b * z - c * y + d * x).natAbs ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  rw [← Int.natCast_inj]
  push_cast
  simp only [sq_abs, _root_.euler_four_squares]

namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : 2 * m = x ^ 2 + y ^ 2) :
    m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
  have : Even (x ^ 2 + y ^ 2) := by simp [← h]
  mul_right_injective₀ (show (2 * 2 : ℤ) ≠ 0 by decide) <|
    calc
      2 * 2 * m = (x - y) ^ 2 + (x + y) ^ 2 := by rw [mul_assoc, h]; ring
      _ = (2 * ((x - y) / 2)) ^ 2 + (2 * ((x + y) / 2)) ^ 2 := by
        rw [Int.mul_ediv_cancel' _, Int.mul_ediv_cancel' _] <;>
          simpa [sq, parity_simps, ← even_iff_two_dvd]
      _ = 2 * 2 * (((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2) := by nlinarith

theorem lt_of_sum_four_squares_eq_mul {a b c d k m : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k * m)
    (ha : 2 * a < m) (hb : 2 * b < m) (hc : 2 * c < m) (hd : 2 * d < m) :
    k < m := by nlinarith

theorem exists_sq_add_sq_add_one_eq_mul (p : ℕ) [hp : Fact p.Prime] :
    ∃ (a b k : ℕ), 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p := by
  rcases hp.1.eq_two_or_odd' with (rfl | hodd)
  · use 1, 0, 1; simp
  rcases Nat.sq_add_sq_zmodEq p (-1) with ⟨a, b, ha, hb, hab⟩
  rcases Int.modEq_iff_dvd.1 hab.symm with ⟨k, hk⟩
  rw [sub_neg_eq_add, mul_comm] at hk
  have hk₀ : 0 < k := by
    refine pos_of_mul_pos_left ?_ (Nat.cast_nonneg p)
    rw [← hk]
    positivity
  lift k to ℕ using hk₀.le
  refine ⟨a, b, k, Nat.cast_pos.1 hk₀, ?_, mod_cast hk⟩
  replace hk : a ^ 2 + b ^ 2 + 1 ^ 2 + 0 ^ 2 = k * p := mod_cast hk
  refine lt_of_sum_four_squares_eq_mul hk ?_ ?_ ?_ ?_
  · exact (mul_le_mul' le_rfl ha).trans_lt (Nat.mul_div_lt_iff_not_dvd.2 hodd.not_two_dvd_nat)
  · exact (mul_le_mul' le_rfl hb).trans_lt (Nat.mul_div_lt_iff_not_dvd.2 hodd.not_two_dvd_nat)
  · exact lt_of_le_of_ne hp.1.two_le (hodd.ne_two_of_dvd_nat (dvd_refl _)).symm
  · exact hp.1.pos

end Int

namespace Nat

open Int

private theorem sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) :
    ∃ w x y z : ℤ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have : ∀ f : Fin 4 → ZMod 2, f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2 = 0 → ∃ i : Fin 4,
      f i ^ 2 + f (swap i 0 1) ^ 2 = 0 ∧ f (swap i 0 2) ^ 2 + f (swap i 0 3) ^ 2 = 0 := by
    decide
  set f : Fin 4 → ℤ := ![a, b, c, d]
  obtain ⟨i, hσ⟩ := this (fun x => ↑(f x)) <| by
    rw [← @zero_mul (ZMod 2) _ m, ← show ((2 : ℤ) : ZMod 2) = 0 from rfl, ← Int.cast_mul, ← h]
    simp only [Int.cast_add, Int.cast_pow]
    rfl
  set σ := swap i 0
  obtain ⟨x, hx⟩ : (2 : ℤ) ∣ f (σ 0) ^ 2 + f (σ 1) ^ 2 :=
    (CharP.intCast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [σ, Int.cast_pow, Int.cast_add, Equiv.swap_apply_right, ZMod.pow_card] using hσ.1
  obtain ⟨y, hy⟩ : (2 : ℤ) ∣ f (σ 2) ^ 2 + f (σ 3) ^ 2 :=
    (CharP.intCast_eq_zero_iff (ZMod 2) 2 _).1 <| by
      simpa only [Int.cast_pow, Int.cast_add, ZMod.pow_card] using hσ.2
  refine ⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0) + f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2,
    (f (σ 2) + f (σ 3)) / 2, ?_⟩
  rw [← Int.sq_add_sq_of_two_mul_sq_add_sq hx.symm, add_assoc,
    ← Int.sq_add_sq_of_two_mul_sq_add_sq hy.symm, ← mul_right_inj' two_ne_zero, ← h, mul_add]
  have : (∑ x, f (σ x) ^ 2) = ∑ x, f x ^ 2 := Equiv.sum_comp σ (f · ^ 2)
  simpa only [← hx, ← hy, Fin.sum_univ_four, add_assoc] using this

/-- Lagrange's **four squares theorem** for a prime number. Use `Nat.sum_four_squares` instead. -/
protected theorem Prime.sum_four_squares {p : ℕ} (hp : p.Prime) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = p := by
  classical
  have := Fact.mk hp
  -- Find `a`, `b`, `c`, `d`, `0 < m < p` such that `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p`
  have natAbs_iff {a b c d : ℤ} {k : ℕ} :
      a.natAbs ^ 2 + b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = k ↔
        a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k := by
    rw [← @Nat.cast_inj ℤ]; push_cast [sq_abs]; rfl
  have hm : ∃ m < p, 0 < m ∧ ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m * p := by
    obtain ⟨a, b, k, hk₀, hkp, hk⟩ := exists_sq_add_sq_add_one_eq_mul p
    refine ⟨k, hkp, hk₀, a, b, 1, 0, ?_⟩
    simpa
  -- Take the minimal possible `m`
  rcases Nat.findX hm with ⟨m, ⟨hmp, hm₀, a, b, c, d, habcd⟩, hmin⟩
  -- If `m = 1`, then we are done
  rcases (Nat.one_le_iff_ne_zero.2 hm₀.ne').eq_or_lt with rfl | hm₁
  · use a, b, c, d; simpa using habcd
  -- Otherwise, let us find a contradiction
  exfalso
  have : NeZero m := ⟨hm₀.ne'⟩
  by_cases hm : 2 ∣ m
  · -- If `m` is an even number, then `(m / 2) * p` can be represented as a sum of four squares
    rcases hm with ⟨m, rfl⟩
    rw [mul_pos_iff_of_pos_left two_pos] at hm₀
    have hm₂ : m < 2 * m := by simpa [two_mul]
    apply_fun (Nat.cast : ℕ → ℤ) at habcd
    push_cast [mul_assoc] at habcd
    obtain ⟨_, _, _, _, h⟩ := sum_four_squares_of_two_mul_sum_four_squares habcd
    exact hmin m hm₂ ⟨hm₂.trans hmp, hm₀, _, _, _, _, natAbs_iff.2 h⟩
  · -- For each `x` in `a`, `b`, `c`, `d`, take a number `f x ≡ x [ZMOD m]` with least possible
    -- absolute value
    obtain ⟨f, hf_lt, hf_mod⟩ :
        ∃ f : ℕ → ℤ, (∀ x, 2 * (f x).natAbs < m) ∧ ∀ x, (f x : ZMod m) = x := by
      refine ⟨fun x ↦ (x : ZMod m).valMinAbs, fun x ↦ ?_, fun x ↦ (x : ZMod m).coe_valMinAbs⟩
      exact (mul_le_mul' le_rfl (x : ZMod m).natAbs_valMinAbs_le).trans_lt
        (Nat.mul_div_lt_iff_not_dvd.2 hm)
    -- Since `|f x| ^ 2 = (f x) ^ 2 ≡ x ^ 2 [ZMOD m]`, we have
    -- `m ∣ |f a| ^ 2 + |f b| ^ 2 + |f c| ^ 2 + |f d| ^ 2`
    obtain ⟨r, hr⟩ :
        m ∣ (f a).natAbs ^ 2 + (f b).natAbs ^ 2 + (f c).natAbs ^ 2 + (f d).natAbs ^ 2 := by
      simp only [← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast [hf_mod, sq_abs]
      norm_cast
      simp [habcd]
    -- The quotient `r` is not zero, because otherwise `f a = f b = f c = f d = 0`, hence
    -- `m` divides each `a`, `b`, `c`, `d`, thus `m ∣ p` which is impossible.
    rcases (zero_le r).eq_or_lt with rfl | hr₀
    · replace hr : f a = 0 ∧ f b = 0 ∧ f c = 0 ∧ f d = 0 := by simpa [and_assoc] using hr
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ⟨d, rfl⟩⟩ : m ∣ a ∧ m ∣ b ∧ m ∣ c ∧ m ∣ d := by
        simp only [← ZMod.natCast_eq_zero_iff, ← hf_mod, hr, Int.cast_zero, and_self]
      have : m * m ∣ m * p := habcd ▸ ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, by ring⟩
      rw [mul_dvd_mul_iff_left hm₀.ne'] at this
      exact (hp.eq_one_or_self_of_dvd _ this).elim hm₁.ne' hmp.ne
    -- Since `2 * |f x| < m` for each `x ∈ {a, b, c, d}`, we have `r < m`
    have hrm : r < m := by
      rw [mul_comm] at hr
      apply lt_of_sum_four_squares_eq_mul hr <;> apply hf_lt
    -- Now it suffices to represent `r * p` as a sum of four squares
    -- More precisely, we will represent `(m * r) * (m * p)` as a sum of squares of four numbers,
    -- each of them is divisible by `m`
    rsuffices ⟨w, x, y, z, hw, hx, hy, hz, h⟩ : ∃ w x y z : ℤ, ↑m ∣ w ∧ ↑m ∣ x ∧ ↑m ∣ y ∧ ↑m ∣ z ∧
      w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = ↑(m * r) * ↑(m * p)
    · have : (w / m) ^ 2 + (x / m) ^ 2 + (y / m) ^ 2 + (z / m) ^ 2 = ↑(r * p) := by
        refine mul_left_cancel₀ (pow_ne_zero 2 (Nat.cast_ne_zero.2 hm₀.ne')) ?_
        conv_rhs => rw [← Nat.cast_pow, ← Nat.cast_mul, sq m, mul_mul_mul_comm, Nat.cast_mul, ← h]
        simp only [mul_add, ← mul_pow, Int.mul_ediv_cancel', *]
      rw [← natAbs_iff] at this
      exact hmin r hrm ⟨hrm.trans hmp, hr₀, _, _, _, _, this⟩
    -- To do the last step, we apply the Euler's four square identity once more
    replace hr : (f b) ^ 2 + (f a) ^ 2 + (f d) ^ 2 + (-f c) ^ 2 = ↑(m * r) := by
      rw [← natAbs_iff, natAbs_neg, ← hr]
      ac_rfl
    have := congr_arg₂ (· * Nat.cast ·) hr habcd
    simp only [← _root_.euler_four_squares, Nat.cast_add, Nat.cast_pow] at this
    refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, this⟩
    · simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]
    · suffices ((a : ZMod m) ^ 2 + (b : ZMod m) ^ 2 + (c : ZMod m) ^ 2 + (d : ZMod m) ^ 2) = 0 by
        simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd, hf_mod, sq, add_comm, add_assoc,
          add_left_comm] using this
      norm_cast
      simp [habcd]
    · simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]
    · simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, hf_mod, mul_comm]

/-- **Four squares theorem** -/
@[informal "sum of four squares"]
@[informal "sum of four squares"]
theorem sum_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  -- The proof is by induction on prime factorization. The case of prime `n` was proved above,
  -- the inductive step follows from `Nat.euler_four_squares`.
  induction n using Nat.recOnMul with
  | zero => exact ⟨0, 0, 0, 0, rfl⟩
  | one => exact ⟨1, 0, 0, 0, rfl⟩
  | prime p hp => exact hp.sum_four_squares
  | mul m n hm hn =>
    rcases hm with ⟨a, b, c, d, rfl⟩
    rcases hn with ⟨w, x, y, z, rfl⟩
    exact ⟨_, _, _, _, euler_four_squares _ _ _ _ _ _ _ _⟩

end Nat
