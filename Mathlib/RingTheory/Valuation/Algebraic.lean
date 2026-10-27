/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.RingTheory.Algebraic.Integral

/-!
# Valuation of an algebraic element

The valuation of an element `x` algebraic over a field `K` is an `n`-th root of
the valuation of some element of `K`, for some positive integer `n`
at most the degree of `x` over `K`.
-/

namespace Valuation

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation A Γ)

/-- If `x` is algebraic over `K`, then `v x` is an `n`-th root of some `v (algebraMap K A r)`. -/
public theorem exists_map_pow_eq_map_algebraMap_of_isAlgebraic {x : A} (hx : IsAlgebraic K x) :
    ∃ (n : ℕ) (r : K), 0 < n ∧ n ≤ (minpoly K x).natDegree ∧ v x ^ n = v (algebraMap K A r) := by
  have : Nontrivial A := ⟨0, 1, ne_of_apply_ne v (by simp)⟩
  obtain hx0 | hx0 := eq_or_ne (v x) 0
  · exact ⟨1, 0, one_pos, Nat.one_le_of_lt (minpoly.natDegree_pos hx.isIntegral), by simp [hx0]⟩
  obtain ⟨p, hpm, hne⟩ := hx.isIntegral
  have hne := minpoly.aeval K x
  rw [Polynomial.aeval_eq_sum_range] at hne
  obtain ⟨i, hid, j, hjd, hij, hi0, hj0, hv⟩ :=
    exists_map_eq_of_map_sum_eq_zero v (Finset.self_mem_range_succ (minpoly K x).natDegree)
      (by simp [minpoly.monic hx.isIntegral, hx0]) ((congrArg v hne).trans (map_zero v))
  simp only [Algebra.smul_def, map_mul, map_pow] at hv
  rw [Finset.mem_range, Nat.lt_add_one_iff] at hid hjd
  wlog hji : j < i generalizing i j with ih
  · exact ih j hjd i hid hij.symm hj0 hi0 hv.symm (by order)
  refine ⟨i - j, (minpoly K x).coeff j / (minpoly K x).coeff i,
    Nat.sub_pos_of_lt hji, (Nat.sub_le _ _).trans hid, ?_⟩
  rw [pow_sub_of_lt (v x) hji, ← comap_apply, map_div₀, comap_apply, comap_apply, ← div_eq_mul_inv]
  refine (div_eq_div_iff ?_ ?_).2 ((mul_comm _ _).trans hv)
  · simp [hx0]
  · rw [Algebra.smul_def, map_mul, map_pow, mul_ne_zero_iff] at hi0
    exact hi0.left

end Valuation
