/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.convex.specific_functions.deriv
! leanprover-community/mathlib commit a16665637b378379689c566204817ae792ac8b39
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Deriv.Zpow
import Mathbin.Analysis.SpecialFunctions.Pow.Deriv
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Collection of convex functions

In this file we prove that certain specific functions are strictly convex, including the following:

* `even.strict_convex_on_pow` : For an even `n : ℕ` with `2 ≤ n`, `λ x, x ^ n` is strictly convex.
* `strict_convex_on_pow` : For `n : ℕ`, with `2 ≤ n`, `λ x, x ^ n` is strictly convex on $[0, +∞)$.
* `strict_convex_on_zpow` : For `m : ℤ` with `m ≠ 0, 1`, `λ x, x ^ m` is strictly convex on
  $[0, +∞)$.
* `strict_concave_on_sin_Icc` : `sin` is strictly concave on $[0, π]$
* `strict_concave_on_cos_Icc` : `cos` is strictly concave on $[-π/2, π/2]$

## TODO

These convexity lemmas are proved by checking the sign of the second derivative.  If desired, most
of these could also be switched to elementary proofs, like in
`analysis.convex.specific_functions.basic`.

-/


open Real Set

open scoped BigOperators NNReal

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
theorem strictConvexOn_pow {n : ℕ} (hn : 2 ≤ n) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n :=
  by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  rw [deriv_pow', interior_Ici]
  exact fun x (hx : 0 < x) y hy hxy =>
    mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le <| Nat.sub_pos_of_lt hn)
      (Nat.cast_pos.2 <| zero_lt_two.trans_le hn)
#align strict_convex_on_pow strictConvexOn_pow

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
theorem Even.strictConvexOn_pow {n : ℕ} (hn : Even n) (h : n ≠ 0) :
    StrictConvexOn ℝ Set.univ fun x : ℝ => x ^ n :=
  by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  rw [deriv_pow']
  replace h := Nat.pos_of_ne_zero h
  exact
    StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
      (Nat.cast_pos.2 h)
#align even.strict_convex_on_pow Even.strictConvexOn_pow

theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type _} [LinearOrderedCommRing β] {f : α → β}
    [DecidablePred fun x => f x ≤ 0] {s : Finset α} (h0 : Even (s.filterₓ fun x => f x ≤ 0).card) :
    0 ≤ ∏ x in s, f x :=
  calc
    0 ≤ ∏ x in s, (if f x ≤ 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by split_ifs with hx hx; · simp [hx]; simp at hx ⊢;
        exact le_of_lt hx
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, neg_one_pow_eq_pow_mod_two, Nat.even_iff.1 h0, pow_zero, one_mul]
    
#align finset.prod_nonneg_of_card_nonpos_even Finset.prod_nonneg_of_card_nonpos_even

theorem int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : Even n) : 0 ≤ ∏ k in Finset.range n, m - k :=
  by
  rcases hn with ⟨n, rfl⟩
  induction' n with n ihn; · simp
  rw [← two_mul] at ihn 
  rw [← two_mul, Nat.succ_eq_add_one, mul_add, mul_one, bit0, ← add_assoc, Finset.prod_range_succ,
    Finset.prod_range_succ, mul_assoc]
  refine' mul_nonneg ihn _; generalize (1 + 1) * n = k
  cases' le_or_lt m k with hmk hmk
  · have : m ≤ k + 1 := hmk.trans (lt_add_one ↑k).le
    convert mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
    convert sub_nonpos_of_le this
  · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)
#align int_prod_range_nonneg int_prod_range_nonneg

theorem int_prod_range_pos {m : ℤ} {n : ℕ} (hn : Even n) (hm : m ∉ Ico (0 : ℤ) n) :
    0 < ∏ k in Finset.range n, m - k :=
  by
  refine' (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm _
  rw [eq_comm, Finset.prod_eq_zero_iff] at h 
  obtain ⟨a, ha, h⟩ := h
  rw [sub_eq_zero.1 h]
  exact ⟨Int.ofNat_zero_le _, Int.ofNat_lt.2 <| Finset.mem_range.1 ha⟩
#align int_prod_range_pos int_prod_range_pos

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
theorem strictConvexOn_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
    StrictConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ m :=
  by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · exact (continuousOn_zpow₀ m).mono fun x hx => ne_of_gt hx
  intro x hx
  rw [iter_deriv_zpow]
  refine' mul_pos _ (zpow_pos_of_pos hx _)
  exact_mod_cast int_prod_range_pos (even_bit0 1) fun hm => _
  norm_cast at hm 
  rw [← Finset.coe_Ico] at hm 
  fin_cases hm <;> cc
#align strict_convex_on_zpow strictConvexOn_zpow

section SqrtMulLog

theorem hasDerivAt_sqrt_mul_log {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => sqrt x * log x) ((2 + log x) / (2 * sqrt x)) x :=
  by
  convert (has_deriv_at_sqrt hx).mul (has_deriv_at_log hx)
  rw [add_div, div_mul_right (sqrt x) two_ne_zero, ← div_eq_mul_inv, sqrt_div_self', add_comm,
    div_eq_mul_one_div, mul_comm]
#align has_deriv_at_sqrt_mul_log hasDerivAt_sqrt_mul_log

theorem deriv_sqrt_mul_log (x : ℝ) :
    deriv (fun x => sqrt x * log x) x = (2 + log x) / (2 * sqrt x) :=
  by
  cases' lt_or_le 0 x with hx hx
  · exact (hasDerivAt_sqrt_mul_log hx.ne').deriv
  · rw [sqrt_eq_zero_of_nonpos hx, MulZeroClass.mul_zero, div_zero]
    refine' HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffOn_Iic 0 x hx)
    refine' (hasDerivWithinAt_const x _ 0).congr_of_mem (fun x hx => _) hx
    rw [sqrt_eq_zero_of_nonpos hx, MulZeroClass.zero_mul]
#align deriv_sqrt_mul_log deriv_sqrt_mul_log

theorem deriv_sqrt_mul_log' :
    (deriv fun x => sqrt x * log x) = fun x => (2 + log x) / (2 * sqrt x) :=
  funext deriv_sqrt_mul_log
#align deriv_sqrt_mul_log' deriv_sqrt_mul_log'

theorem deriv2_sqrt_mul_log (x : ℝ) :
    (deriv^[2]) (fun x => sqrt x * log x) x = -log x / (4 * sqrt x ^ 3) :=
  by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  cases' le_or_lt x 0 with hx hx
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow zero_lt_three, MulZeroClass.mul_zero, div_zero]
    refine' HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffOn_Iic 0 x hx)
    refine' (hasDerivWithinAt_const _ _ 0).congr_of_mem (fun x hx => _) hx
    rw [sqrt_eq_zero_of_nonpos hx, MulZeroClass.mul_zero, div_zero]
  · have h₀ : sqrt x ≠ 0 := sqrt_ne_zero'.2 hx
    convert
      (((has_deriv_at_log hx.ne').const_add 2).div ((has_deriv_at_sqrt hx.ne').const_mul 2) <|
          mul_ne_zero two_ne_zero h₀).deriv using
      1
    nth_rw 3 [← mul_self_sqrt hx.le]
    field_simp; ring
#align deriv2_sqrt_mul_log deriv2_sqrt_mul_log

theorem strictConcaveOn_sqrt_mul_log_Ioi : StrictConcaveOn ℝ (Set.Ioi 1) fun x => sqrt x * log x :=
  by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => _
  ·
    exact
      continuous_sqrt.continuous_on.mul
        (continuous_on_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    exact
      div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
        (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))
#align strict_concave_on_sqrt_mul_log_Ioi strictConcaveOn_sqrt_mul_log_Ioi

end SqrtMulLog

open scoped Real

theorem strictConcaveOn_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin :=
  by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuous_on_sin fun x hx => _
  rw [interior_Icc] at hx 
  simp [sin_pos_of_mem_Ioo hx]
#align strict_concave_on_sin_Icc strictConcaveOn_sin_Icc

theorem strictConcaveOn_cos_Icc : StrictConcaveOn ℝ (Icc (-(π / 2)) (π / 2)) cos :=
  by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuous_on_cos fun x hx => _
  rw [interior_Icc] at hx 
  simp [cos_pos_of_mem_Ioo hx]
#align strict_concave_on_cos_Icc strictConcaveOn_cos_Icc

