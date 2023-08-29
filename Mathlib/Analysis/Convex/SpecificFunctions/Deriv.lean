/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

#align_import analysis.convex.specific_functions.deriv from "leanprover-community/mathlib"@"a16665637b378379689c566204817ae792ac8b39"

/-!
# Collection of convex functions

In this file we prove that certain specific functions are strictly convex, including the following:

* `Even.strictConvexOn_pow` : For an even `n : ℕ` with `2 ≤ n`, `fun x => x ^ n` is strictly convex.
* `strictConvexOn_pow` : For `n : ℕ`, with `2 ≤ n`, `fun x => x ^ n` is strictly convex on $[0,+∞)$.
* `strictConvexOn_zpow` : For `m : ℤ` with `m ≠ 0, 1`, `fun x => x ^ m` is strictly convex on
  $[0, +∞)$.
* `strictConcaveOn_sin_Icc` : `sin` is strictly concave on $[0, π]$
* `strictConcaveOn_cos_Icc` : `cos` is strictly concave on $[-π/2, π/2]$

## TODO

These convexity lemmas are proved by checking the sign of the second derivative. If desired, most
of these could also be switched to elementary proofs, like in
`Analysis.Convex.SpecificFunctions.Basic`.

-/


open Real Set

open scoped BigOperators NNReal

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- `x^n`, `n : ℕ` is strictly convex on `[0, +∞)` for all `n` greater than `2`. -/
theorem strictConvexOn_pow {n : ℕ} (hn : 2 ≤ n) : StrictConvexOn ℝ (Ici 0) fun x : ℝ => x ^ n := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) (continuousOn_pow _)
  -- ⊢ StrictMonoOn (deriv fun x => x ^ n) (interior (Ici 0))
  rw [deriv_pow', interior_Ici]
  -- ⊢ StrictMonoOn (fun x => ↑n * x ^ (n - 1)) (Ioi 0)
  exact fun x (hx : 0 < x) y hy hxy =>
    mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_left hxy hx.le <| Nat.sub_pos_of_lt hn)
      (Nat.cast_pos.2 <| zero_lt_two.trans_le hn)
#align strict_convex_on_pow strictConvexOn_pow

/-- `x^n`, `n : ℕ` is strictly convex on the whole real line whenever `n ≠ 0` is even. -/
theorem Even.strictConvexOn_pow {n : ℕ} (hn : Even n) (h : n ≠ 0) :
    StrictConvexOn ℝ Set.univ fun x : ℝ => x ^ n := by
  apply StrictMono.strictConvexOn_univ_of_deriv (continuous_pow n)
  -- ⊢ StrictMono (deriv fun a => a ^ n)
  rw [deriv_pow']
  -- ⊢ StrictMono fun x => ↑n * x ^ (n - 1)
  replace h := Nat.pos_of_ne_zero h
  -- ⊢ StrictMono fun x => ↑n * x ^ (n - 1)
  exact StrictMono.const_mul (Odd.strictMono_pow <| Nat.Even.sub_odd h hn <| Nat.odd_iff.2 rfl)
    (Nat.cast_pos.2 h)
#align even.strict_convex_on_pow Even.strictConvexOn_pow

theorem Finset.prod_nonneg_of_card_nonpos_even {α β : Type*} [LinearOrderedCommRing β] {f : α → β}
    [DecidablePred fun x => f x ≤ 0] {s : Finset α} (h0 : Even (s.filter fun x => f x ≤ 0).card) :
    0 ≤ ∏ x in s, f x :=
  calc
    0 ≤ ∏ x in s, (if f x ≤ 0 then (-1 : β) else 1) * f x :=
      Finset.prod_nonneg fun x _ => by
        split_ifs with hx
        -- ⊢ 0 ≤ -1 * f x
        · simp [hx]
          -- 🎉 no goals
        simp at hx ⊢
        -- ⊢ 0 ≤ f x
        exact le_of_lt hx
        -- 🎉 no goals
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, neg_one_pow_eq_pow_mod_two, Nat.even_iff.1 h0, pow_zero, one_mul]
#align finset.prod_nonneg_of_card_nonpos_even Finset.prod_nonneg_of_card_nonpos_even

theorem int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : Even n) :
    0 ≤ ∏ k in Finset.range n, (m - k) := by
  rcases hn with ⟨n, rfl⟩
  -- ⊢ 0 ≤ ∏ k in Finset.range (n + n), (m - ↑k)
  induction' n with n ihn
  -- ⊢ 0 ≤ ∏ k in Finset.range (Nat.zero + Nat.zero), (m - ↑k)
  · simp
    -- 🎉 no goals
  rw [← two_mul] at ihn
  -- ⊢ 0 ≤ ∏ k in Finset.range (Nat.succ n + Nat.succ n), (m - ↑k)
  rw [← two_mul, Nat.succ_eq_add_one, mul_add, mul_one, ← one_add_one_eq_two, ← add_assoc,
    Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc]
  refine' mul_nonneg ihn _; generalize (1 + 1) * n = k
  -- ⊢ 0 ≤ (m - ↑((1 + 1) * n)) * (m - ↑((1 + 1) * n + 1))
                            -- ⊢ 0 ≤ (m - ↑k) * (m - ↑(k + 1))
  cases' le_or_lt m k with hmk hmk
  -- ⊢ 0 ≤ (m - ↑k) * (m - ↑(k + 1))
  · have : m ≤ k + 1 := hmk.trans (lt_add_one (k : ℤ)).le
    -- ⊢ 0 ≤ (m - ↑k) * (m - ↑(k + 1))
    convert mul_nonneg_of_nonpos_of_nonpos (sub_nonpos_of_le hmk) _
    -- ⊢ m - ↑(k + 1) ≤ 0
    convert sub_nonpos_of_le this
    -- 🎉 no goals
  · exact mul_nonneg (sub_nonneg_of_le hmk.le) (sub_nonneg_of_le hmk)
    -- 🎉 no goals
#align int_prod_range_nonneg int_prod_range_nonneg

theorem int_prod_range_pos {m : ℤ} {n : ℕ} (hn : Even n) (hm : m ∉ Ico (0 : ℤ) n) :
    0 < ∏ k in Finset.range n, (m - k) := by
  refine' (int_prod_range_nonneg m n hn).lt_of_ne fun h => hm _
  -- ⊢ m ∈ Ico 0 ↑n
  rw [eq_comm, Finset.prod_eq_zero_iff] at h
  -- ⊢ m ∈ Ico 0 ↑n
  obtain ⟨a, ha, h⟩ := h
  -- ⊢ m ∈ Ico 0 ↑n
  rw [sub_eq_zero.1 h]
  -- ⊢ ↑a ∈ Ico 0 ↑n
  exact ⟨Int.ofNat_zero_le _, Int.ofNat_lt.2 <| Finset.mem_range.1 ha⟩
  -- 🎉 no goals
#align int_prod_range_pos int_prod_range_pos

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` except `0` and `1`. -/
theorem strictConvexOn_zpow {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
    StrictConvexOn ℝ (Ioi 0) fun x : ℝ => x ^ m := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  -- ⊢ ContinuousOn (fun x => x ^ m) (Ioi 0)
  · exact (continuousOn_zpow₀ m).mono fun x hx => ne_of_gt hx
    -- 🎉 no goals
  intro x hx
  -- ⊢ 0 < deriv^[2] (fun x => x ^ m) x
  rw [mem_Ioi] at hx
  -- ⊢ 0 < deriv^[2] (fun x => x ^ m) x
  rw [iter_deriv_zpow]
  -- ⊢ 0 < (∏ i in Finset.range 2, (↑m - ↑i)) * x ^ (m - ↑2)
  refine' mul_pos _ (zpow_pos_of_pos hx _)
  -- ⊢ 0 < ∏ i in Finset.range 2, (↑m - ↑i)
  norm_cast
  -- ⊢ 0 < ∏ i in Finset.range 2, (m - ↑i)
  refine' int_prod_range_pos (by simp only) fun hm => _
  -- ⊢ False
  rw [← Finset.coe_Ico] at hm
  -- ⊢ False
  norm_cast at hm
  -- ⊢ False
  fin_cases hm <;> simp_all -- Porting note: `simp_all` was `cc`
  -- ⊢ False
                   -- 🎉 no goals
                   -- 🎉 no goals
#align strict_convex_on_zpow strictConvexOn_zpow

section SqrtMulLog

theorem hasDerivAt_sqrt_mul_log {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => sqrt x * log x) ((2 + log x) / (2 * sqrt x)) x := by
  convert (hasDerivAt_sqrt hx).mul (hasDerivAt_log hx) using 1
  -- ⊢ (2 + log x) / (2 * sqrt x) = 1 / (2 * sqrt x) * log x + sqrt x * x⁻¹
  rw [add_div, div_mul_right (sqrt x) two_ne_zero, ← div_eq_mul_inv, sqrt_div_self', add_comm,
    div_eq_mul_one_div, mul_comm]
#align has_deriv_at_sqrt_mul_log hasDerivAt_sqrt_mul_log

theorem deriv_sqrt_mul_log (x : ℝ) :
    deriv (fun x => sqrt x * log x) x = (2 + log x) / (2 * sqrt x) := by
  cases' lt_or_le 0 x with hx hx
  -- ⊢ deriv (fun x => sqrt x * log x) x = (2 + log x) / (2 * sqrt x)
  · exact (hasDerivAt_sqrt_mul_log hx.ne').deriv
    -- 🎉 no goals
  · rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    -- ⊢ deriv (fun x => sqrt x * log x) x = 0
    refine' HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffOn_Iic 0 x hx)
    -- ⊢ HasDerivWithinAt (fun x => sqrt x * log x) 0 (Iic 0) x
    refine' (hasDerivWithinAt_const x _ 0).congr_of_mem (fun x hx => _) hx
    -- ⊢ sqrt x * log x = 0
    rw [sqrt_eq_zero_of_nonpos hx, zero_mul]
    -- 🎉 no goals
#align deriv_sqrt_mul_log deriv_sqrt_mul_log

theorem deriv_sqrt_mul_log' :
    (deriv fun x => sqrt x * log x) = fun x => (2 + log x) / (2 * sqrt x) :=
  funext deriv_sqrt_mul_log
#align deriv_sqrt_mul_log' deriv_sqrt_mul_log'

theorem deriv2_sqrt_mul_log (x : ℝ) :
    deriv^[2] (fun x => sqrt x * log x) x = -log x / (4 * sqrt x ^ 3) := by
  simp only [Nat.iterate, deriv_sqrt_mul_log']
  -- ⊢ deriv (fun x => (2 + log x) / (2 * sqrt x)) x = -log x / (↑4 * sqrt x ^ 3)
  cases' le_or_lt x 0 with hx hx
  -- ⊢ deriv (fun x => (2 + log x) / (2 * sqrt x)) x = -log x / (↑4 * sqrt x ^ 3)
  · rw [sqrt_eq_zero_of_nonpos hx, zero_pow zero_lt_three, mul_zero, div_zero]
    -- ⊢ deriv (fun x => (2 + log x) / (2 * sqrt x)) x = 0
    refine' HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffOn_Iic 0 x hx)
    -- ⊢ HasDerivWithinAt (fun x => (2 + log x) / (2 * sqrt x)) 0 (Iic 0) x
    refine' (hasDerivWithinAt_const _ _ 0).congr_of_mem (fun x hx => _) hx
    -- ⊢ (2 + log x) / (2 * sqrt x) = 0
    rw [sqrt_eq_zero_of_nonpos hx, mul_zero, div_zero]
    -- 🎉 no goals
  · have h₀ : sqrt x ≠ 0 := sqrt_ne_zero'.2 hx
    -- ⊢ deriv (fun x => (2 + log x) / (2 * sqrt x)) x = -log x / (↑4 * sqrt x ^ 3)
    convert (((hasDerivAt_log hx.ne').const_add 2).div ((hasDerivAt_sqrt hx.ne').const_mul 2) <|
      mul_ne_zero two_ne_zero h₀).deriv using 1
    nth_rw 3 [← mul_self_sqrt hx.le]
    -- ⊢ -log x / (↑4 * sqrt x ^ 3) = ((sqrt x * sqrt x)⁻¹ * (2 * sqrt x) - (2 + log  …
    generalize sqrt x = sqx at h₀ -- else field_simp rewrites sqrt x * sqrt x back to x
    -- ⊢ -log x / (↑4 * sqx ^ 3) = ((sqx * sqx)⁻¹ * (2 * sqx) - (2 + log x) * (2 * (1 …
    field_simp
    -- ⊢ -(log x * (sqx * sqx * (2 * sqx) * (2 * sqx) ^ 2)) = (2 * sqx * (2 * sqx) -  …
    ring
    -- 🎉 no goals
#align deriv2_sqrt_mul_log deriv2_sqrt_mul_log

theorem strictConcaveOn_sqrt_mul_log_Ioi :
    StrictConcaveOn ℝ (Set.Ioi 1) fun x => sqrt x * log x := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 1) _ fun x hx => ?_
  -- ⊢ ContinuousOn (fun x => sqrt x * log x) (Ioi 1)
  · exact continuous_sqrt.continuousOn.mul
      (continuousOn_log.mono fun x hx => ne_of_gt (zero_lt_one.trans hx))
  · rw [deriv2_sqrt_mul_log x]
    -- ⊢ -log x / (↑4 * sqrt x ^ 3) < 0
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (log_pos hx))
      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))
#align strict_concave_on_sqrt_mul_log_Ioi strictConcaveOn_sqrt_mul_log_Ioi

end SqrtMulLog

open scoped Real

theorem strictConcaveOn_sin_Icc : StrictConcaveOn ℝ (Icc 0 π) sin := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_sin fun x hx => ?_
  -- ⊢ deriv^[2] sin x < 0
  rw [interior_Icc] at hx
  -- ⊢ deriv^[2] sin x < 0
  simp [sin_pos_of_mem_Ioo hx]
  -- 🎉 no goals
#align strict_concave_on_sin_Icc strictConcaveOn_sin_Icc

theorem strictConcaveOn_cos_Icc : StrictConcaveOn ℝ (Icc (-(π / 2)) (π / 2)) cos := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuousOn_cos fun x hx => ?_
  -- ⊢ deriv^[2] cos x < 0
  rw [interior_Icc] at hx
  -- ⊢ deriv^[2] cos x < 0
  simp [cos_pos_of_mem_Ioo hx]
  -- 🎉 no goals
#align strict_concave_on_cos_Icc strictConcaveOn_cos_Icc
