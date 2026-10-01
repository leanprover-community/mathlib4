/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.RingTheory.Algebraic.Integral

/-!
# Valuation of an algebraic element

The valuation of an algebraic element is an n-th root of
the valuation of an element in the base field.
-/

namespace Valuation

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation A Γ)

/-- If `x` is algebraic over `K`, then `v x` is an n-th root of some `v (algebraMap K A r)`. -/
public theorem exists_pow_eq_of_isAlgebraic {x : A} (hx : IsAlgebraic K x) :
    ∃ (n : ℕ) (r : K), n ≠ 0 ∧ v x ^ n = v (algebraMap K A r) := by
  classical
  obtain hx0 | hx0 := eq_or_ne (v x) 0
  · exact ⟨1, 0, by simp [hx0]⟩
  obtain ⟨p, hpm, hne⟩ := hx.isIntegral
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range] at hne
  obtain ⟨i, -, j, -, hij, hi0, hj0, hv⟩ :=
    exists_map_eq_of_sum_eq_zero v ⟨p.natDegree, by simp [hpm, hx0]⟩ hne
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_pow, map_pow] at hv
  wlog hji : j < i generalizing i j with ih
  · exact (ih j i hij.symm hj0 hi0 hv.symm ((lt_trichotomy i j).resolve_right (·.elim hij hji)))
  refine ⟨i - j, p.coeff j / p.coeff i, Nat.sub_ne_zero_of_lt hji, ?_⟩
  rw [pow_sub_of_lt (v x) hji, ← comap_apply, map_div₀, comap_apply, comap_apply, ← div_eq_mul_inv]
  refine (div_eq_div_iff ?_ ?_).2 ((mul_comm _ _).trans hv)
  · simp [hx0]
  · rw [Algebra.smul_def, map_mul, map_pow, mul_ne_zero_iff] at hi0
    exact hi0.left

end Valuation
