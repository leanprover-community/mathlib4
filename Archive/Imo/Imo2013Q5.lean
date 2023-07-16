/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw

! This file was ported from Lean 3 source module imo.imo2013_q5
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# IMO 2013 Q5

Let `ℚ>₀` be the positive rational numbers. Let `f : ℚ>₀ → ℝ` be a function satisfying
the conditions

1. `f(x) * f(y) ≥ f(x * y)`
2. `f(x + y) ≥ f(x) + f(y)`

for all `x, y ∈ ℚ>₀`. Given that `f(a) = a` for some rational `a > 1`, prove that `f(x) = x` for
all `x ∈ ℚ>₀`.

# Solution

We provide a direct translation of the solution found in
https://www.imo-official.org/problems/IMO2013SL.pdf
-/


open scoped BigOperators

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

namespace Imo2013Q5

theorem le_of_all_pow_lt_succ {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (h : ∀ n : ℕ, 0 < n → x ^ n - 1 < y ^ n) : x ≤ y := by
  by_contra' hxy
  have hxmy : 0 < x - y := sub_pos.mpr hxy
  have hn : ∀ n : ℕ, 0 < n → (x - y) * (n : ℝ) ≤ x ^ n - y ^ n := by
    intro n _
    have hterm : ∀ i : ℕ, i ∈ Finset.range n → 1 ≤ x ^ i * y ^ (n - 1 - i) := by
      intro i _
      have hx' : 1 ≤ x ^ i := one_le_pow_of_one_le hx.le i
      have hy' : 1 ≤ y ^ (n - 1 - i) := one_le_pow_of_one_le hy.le (n - 1 - i)
      calc
        1 ≤ x ^ i := hx'
        _ = x ^ i * 1 := (mul_one _).symm
        _ ≤ x ^ i * y ^ (n - 1 - i) := mul_le_mul_of_nonneg_left hy' (zero_le_one.trans hx')
    calc
      (x - y) * (n : ℝ) = (n : ℝ) * (x - y) := mul_comm _ _
      _ = (∑ _i : ℕ in Finset.range n, (1 : ℝ)) * (x - y) := by
        simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      _ ≤ (∑ i : ℕ in Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y) :=
        ((mul_le_mul_right hxmy).mpr (Finset.sum_le_sum hterm))
      _ = x ^ n - y ^ n := geom_sum₂_mul x y n
  -- Choose n larger than 1 / (x - y).
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - y))
  have hNp : 0 < N := by exact_mod_cast (one_div_pos.mpr hxmy).trans hN
  have :=
    calc
      1 = (x - y) * (1 / (x - y)) := by field_simp [ne_of_gt hxmy]
      _ < (x - y) * N := ((mul_lt_mul_left hxmy).mpr hN)
      _ ≤ x ^ N - y ^ N := hn N hNp
  linarith [h N hNp]
#align imo2013_q5.le_of_all_pow_lt_succ Imo2013Q5.le_of_all_pow_lt_succ

/-- Like `le_of_all_pow_lt_succ`, but with a weaker assumption for y.
-/
theorem le_of_all_pow_lt_succ' {x y : ℝ} (hx : 1 < x) (hy : 0 < y)
    (h : ∀ n : ℕ, 0 < n → x ^ n - 1 < y ^ n) : x ≤ y := by
  refine' le_of_all_pow_lt_succ hx _ h
  by_contra' hy'' : y ≤ 1
  -- Then there exists y' such that 0 < y ≤ 1 < y' < x.
  let y' := (x + 1) / 2
  have h_y'_lt_x : y' < x := by
    have hh : (x + 1) / 2 < x * 2 / 2 := by linarith
    calc
      y' < x * 2 / 2 := hh
      _ = x := by field_simp
  have h1_lt_y' : 1 < y' := by
    have hh' : 1 * 2 / 2 < (x + 1) / 2 := by linarith
    calc
      1 = 1 * 2 / 2 := by field_simp
      _ < y' := hh'
  have h_y_lt_y' : y < y' := hy''.trans_lt h1_lt_y'
  have hh : ∀ n, 0 < n → x ^ n - 1 < y' ^ n := by
    intro n hn
    calc
      x ^ n - 1 < y ^ n := h n hn
      _ ≤ y' ^ n := pow_le_pow_of_le_left hy.le h_y_lt_y'.le n
  exact h_y'_lt_x.not_le (le_of_all_pow_lt_succ hx h1_lt_y' hh)
#align imo2013_q5.le_of_all_pow_lt_succ' Imo2013Q5.le_of_all_pow_lt_succ'

theorem f_pos_of_pos {f : ℚ → ℝ} {q : ℚ} (hq : 0 < q)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    0 < f q := by
  have num_pos : 0 < q.num := Rat.num_pos_iff_pos.mpr hq
  have hmul_pos :=
    calc
      (0 : ℝ) < q.num := Int.cast_pos.mpr num_pos
      _ = ((q.num.natAbs : ℤ) : ℝ) := (congr_arg Int.cast (Int.natAbs_of_nonneg num_pos.le).symm)
      _ ≤ f q.num.natAbs := (H4 q.num.natAbs ((@Int.natAbs_pos q.num).mpr num_pos.ne.symm))
      _ = f q.num := by rw [Nat.cast_natAbs, abs_of_nonneg num_pos.le]
      _ = f (q * q.den) := by rw [← Rat.mul_den_eq_num]
      _ ≤ f q * f q.den := H1 q q.den hq (Nat.cast_pos.mpr q.pos)
  have h_f_denom_pos :=
    calc
      (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
      _ ≤ f q.den := H4 q.den q.pos
  exact pos_of_mul_pos_left hmul_pos h_f_denom_pos.le
#align imo2013_q5.f_pos_of_pos Imo2013Q5.f_pos_of_pos

theorem fx_gt_xm1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 ≤ x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    (x - 1 : ℝ) < f x := by
  have hx0 :=
    calc
      (x - 1 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.sub_one_lt_floor x
      _ ≤ f ⌊x⌋₊ := H4 _ (Nat.floor_pos.2 hx)
  obtain h_eq | h_lt := (Nat.floor_le <| zero_le_one.trans hx).eq_or_lt
  · rwa [h_eq] at hx0
  calc
    (x - 1 : ℝ) < f ⌊x⌋₊ := hx0
    _ < f (x - ⌊x⌋₊) + f ⌊x⌋₊ := (lt_add_of_pos_left _ (f_pos_of_pos (sub_pos.mpr h_lt) H1 H4))
    _ ≤ f (x - ⌊x⌋₊ + ⌊x⌋₊) := (H2 _ _ (sub_pos.mpr h_lt) (Nat.cast_pos.2 (Nat.floor_pos.2 hx)))
    _ = f x := by rw [sub_add_cancel]
#align imo2013_q5.fx_gt_xm1 Imo2013Q5.fx_gt_xm1

theorem pow_f_le_f_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : 1 < x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :
    f (x ^ n) ≤ f x ^ n := by
  induction' n with pn hpn
  · exfalso; exact Nat.lt_asymm hn hn
  cases' pn with pn
  · norm_num
  have hpn' := hpn pn.succ_pos
  rw [pow_succ' x (pn + 1), pow_succ' (f x) (pn + 1)]
  have hxp : 0 < x := by positivity
  calc
    f (x ^ (pn + 1) * x) ≤ f (x ^ (pn + 1)) * f x := H1 (x ^ (pn + 1)) x (pow_pos hxp (pn + 1)) hxp
    _ ≤ f x ^ (pn + 1) * f x := (mul_le_mul_right (f_pos_of_pos hxp H1 H4)).mpr hpn'
#align imo2013_q5.pow_f_le_f_pow Imo2013Q5.pow_f_le_f_pow

theorem fixed_point_of_pos_nat_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x) {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :
    f (a ^ n) = a ^ n := by
  have hh0 : (a : ℝ) ^ n ≤ f (a ^ n) := by exact_mod_cast H5 (a ^ n) (one_lt_pow ha1 hn.ne')
  have hh1 :=
    calc
      f (a ^ n) ≤ f a ^ n := pow_f_le_f_pow hn ha1 H1 H4
      _ = (a : ℝ) ^ n := by rw [← hae]
  exact_mod_cast hh1.antisymm hh0
#align imo2013_q5.fixed_point_of_pos_nat_pow Imo2013Q5.fixed_point_of_pos_nat_pow

theorem fixed_point_of_gt_1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 < x)
    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)
    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x) {a : ℚ} (ha1 : 1 < a) (hae : f a = a) : f x = x := by
  -- Choose n such that 1 + x < a^n.
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + x) ha1
  have h_big_enough : (1 : ℚ) < a ^ N - x := lt_sub_iff_add_lt.mpr hN
  have h1 :=
    calc
      (x : ℝ) + (a ^ N - x : ℚ) ≤ f x + (a ^ N - x : ℚ) := add_le_add_right (H5 x hx) _
      _ ≤ f x + f (a ^ N - x) := add_le_add_left (H5 _ h_big_enough) _
  have hxp : 0 < x := by positivity
  have hNp : 0 < N := by by_contra' H; rw [le_zero_iff.mp H] at hN; linarith
  have h2 :=
    calc
      f x + f (a ^ N - x) ≤ f (x + (a ^ N - x)) :=
        H2 x (a ^ N - x) hxp (zero_lt_one.trans h_big_enough)
      _ = f (a ^ N) := by ring_nf
      _ = a ^ N := (fixed_point_of_pos_nat_pow hNp H1 H4 H5 ha1 hae)
      _ = x + (a ^ N - x) := by ring
  have heq := h1.antisymm (by exact_mod_cast h2)
  linarith [H5 x hx, H5 _ h_big_enough]
#align imo2013_q5.fixed_point_of_gt_1 Imo2013Q5.fixed_point_of_gt_1

end Imo2013Q5

open Imo2013Q5

theorem imo2013_q5 (f : ℚ → ℝ) (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)
    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H_fixed_point : ∃ a, 1 < a ∧ f a = a) :
    ∀ x, 0 < x → f x = x := by
  obtain ⟨a, ha1, hae⟩ := H_fixed_point
  have H3 : ∀ x : ℚ, 0 < x → ∀ n : ℕ, 0 < n → ↑n * f x ≤ f (n * x) := by
    intro x hx n hn
    cases' n with n
    · exact (lt_irrefl 0 hn).elim
    induction' n with pn hpn
    · norm_num
    calc
      ↑(pn + 2) * f x = (↑pn + 1 + 1) * f x := by norm_cast
      _ = ((pn : ℝ) + 1) * f x + 1 * f x := (add_mul (↑pn + 1) 1 (f x))
      _ = (↑pn + 1) * f x + f x := by rw [one_mul]
      _ ≤ f (↑pn.succ * x) + f x := by exact_mod_cast add_le_add_right (hpn pn.succ_pos) (f x)
      _ ≤ f ((↑pn + 1) * x + x) := by exact_mod_cast H2 _ _ (mul_pos pn.cast_add_one_pos hx) hx
      _ = f ((↑pn + 1) * x + 1 * x) := by rw [one_mul]
      _ = f ((↑pn + 1 + 1) * x) := (congr_arg f (add_mul (↑pn + 1) 1 x).symm)
      _ = f (↑(pn + 2) * x) := by norm_cast
  have H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n := by
    intro n hn
    have hf1 : 1 ≤ f 1 := by
      have a_pos : (0 : ℝ) < a := Rat.cast_pos.mpr (zero_lt_one.trans ha1)
      suffices : ↑a * 1 ≤ ↑a * f 1; exact (mul_le_mul_left a_pos).mp this
      calc
        ↑a * 1 = ↑a := mul_one (a : ℝ)
        _ = f a := hae.symm
        _ = f (a * 1) := by rw [mul_one]
        _ ≤ f a * f 1 := ((H1 a 1) (zero_lt_one.trans ha1) zero_lt_one)
        _ = ↑a * f 1 := by rw [hae]
    calc
      (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) * f 1 := (mul_le_mul_of_nonneg_left hf1 (Nat.cast_nonneg _))
      _ ≤ f (n * 1) := (H3 1 zero_lt_one n hn)
      _ = f n := by rw [mul_one]
  have H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x := by
    intro x hx
    have hxnm1 : ∀ n : ℕ, 0 < n → (x : ℝ) ^ n - 1 < f x ^ n := by
      intro n hn
      calc
        (x : ℝ) ^ n - 1 < f (x ^ n) := by
          exact_mod_cast fx_gt_xm1 (one_le_pow_of_one_le hx.le n) H1 H2 H4
        _ ≤ f x ^ n := pow_f_le_f_pow hn hx H1 H4
    have hx' : 1 < (x : ℝ) := by exact_mod_cast hx
    have hxp : 0 < x := by positivity
    exact le_of_all_pow_lt_succ' hx' (f_pos_of_pos hxp H1 H4) hxnm1
  have h_f_commutes_with_pos_nat_mul : ∀ n : ℕ, 0 < n → ∀ x : ℚ, 0 < x → f (n * x) = n * f x := by
    intro n hn x hx
    have h2 : f (n * x) ≤ n * f x := by
      cases' n with n
      · exfalso; exact Nat.lt_asymm hn hn
      cases' n with n
      · norm_num
      have hfneq : f n.succ.succ = n.succ.succ := by
        have :=
          fixed_point_of_gt_1 (Nat.one_lt_cast.mpr (Nat.succ_lt_succ n.succ_pos)) H1 H2 H4 H5 ha1
            hae
        rwa [Rat.cast_coe_nat n.succ.succ] at this
      rw [← hfneq]
      exact H1 (n.succ.succ : ℚ) x (Nat.cast_pos.mpr hn) hx
    exact h2.antisymm (H3 x hx n hn)
  -- For the final calculation, we expand x as (2 * x.num) / (2 * x.den), because
  -- we need the top of the fraction to be strictly greater than 1 in order
  -- to apply `fixed_point_of_gt_1`.
  intro x hx
  let x2denom := 2 * x.den
  let x2num := 2 * x.num
  have hx2pos :=
    calc
      0 < x.den := x.pos
      _ < x.den + x.den := (lt_add_of_pos_left x.den x.pos)
      _ = 2 * x.den := by ring
  have hxcnez : (x.den : ℚ) ≠ (0 : ℚ) := ne_of_gt (Nat.cast_pos.mpr x.pos)
  have hx2cnezr : (x2denom : ℝ) ≠ (0 : ℝ) := Nat.cast_ne_zero.mpr (ne_of_gt hx2pos)
  have hrat_expand2 :=
    calc
      x = x.num / x.den := by exact_mod_cast Rat.num_den.symm
      _ = x2num / x2denom := by field_simp; linarith
  have h_denom_times_fx :=
    calc
      (x2denom : ℝ) * f x = f (x2denom * x) :=
        (h_f_commutes_with_pos_nat_mul x2denom hx2pos x hx).symm
      _ = f (x2denom * (x2num / x2denom)) := by rw [hrat_expand2]
      _ = f x2num := by congr; field_simp; ring
  have h_fx2num_fixed : f x2num = x2num := by
    have hx2num_gt_one : (1 : ℚ) < (2 * x.num : ℤ) := by
      norm_cast; linarith [Rat.num_pos_iff_pos.mpr hx]
    have hh := fixed_point_of_gt_1 hx2num_gt_one H1 H2 H4 H5 ha1 hae
    rwa [Rat.cast_coe_int x2num] at hh
  calc
    f x = f x * 1 := (mul_one (f x)).symm
    _ = f x * (x2denom / x2denom) := by rw [← div_self hx2cnezr]
    _ = f x * x2denom / x2denom := (mul_div_assoc' (f x) _ _)
    _ = x2denom * f x / x2denom := by rw [mul_comm]
    _ = f x2num / x2denom := by rw [h_denom_times_fx]
    _ = x2num / x2denom := by rw [h_fx2num_fixed]
    _ = (((x2num : ℚ) / (x2denom : ℚ) : ℚ) : ℝ) := by norm_cast
    _ = x := by rw [← hrat_expand2]
#align imo2013_q5 imo2013_q5
