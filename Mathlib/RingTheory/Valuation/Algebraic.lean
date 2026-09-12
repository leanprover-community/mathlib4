/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Valuation of an algebraic element

The valuation of an algebraic element is an n-th root of
the valuation of an element in the base field.
-/

namespace Valuation

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A] [IsDomain A]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation A Γ)

/-- If `x` is algebraic over `K`, then `v x` is an n-th root of some `v (algebraMap K A r)`. -/
public theorem exists_pow_eq_of_isAlgebraic {x : A} (hx : IsAlgebraic K x) :
    ∃ (n : ℕ) (r : K), n ≠ 0 ∧ v x ^ n = v (algebraMap K A r) := by
  classical
  obtain ⟨p, hp0, hne⟩ := hx
  -- assume for sake of contradiction that `v x` is not some n-th root of a `v (algebraMap K A r)`
  contrapose! hne
  have hx0 : v x ≠ 0 := by
    intro h
    simpa [h] using hne 1 0 Nat.one_ne_zero
  apply ne_of_apply_ne v
  rw [Polynomial.aeval_eq_sum_range, ← Finset.sum_filter_ne_zero, map_zero]
  set u : Finset ℕ := (Finset.range (p.natDegree + 1)).filter fun i => p.coeff i • x ^ i ≠ 0
  have hue : u.Nonempty := by
    contrapose! hp0
    rw [Polynomial.ext_iff_natDegree_le le_rfl (by simp)]
    simpa [u, ne_zero_of_map hx0] using hp0
  have hi0 (i : ℕ) (hiu : i ∈ u) : v ((algebraMap K A) (p.coeff i)) ≠ 0 := by
    rw [← comap_apply, ne_zero_iff]
    simp_rw [u, Finset.mem_filter, smul_ne_zero_iff] at hiu
    exact hiu.right.left
  -- let `c` be the number that maximizes `v (p.coeff i • x ^ i)`
  obtain ⟨c, hcu, hc⟩ := Finset.exists_max_image u (fun i => v (p.coeff i • x ^ i)) hue
  replace hc (i : ℕ) (hi : i ∈ u \ {c}) : v (p.coeff i • x ^ i) < v (p.coeff c • x ^ c) := by
    rw [Finset.mem_sdiff, Finset.mem_singleton, ← ne_eq] at hi
    obtain ⟨hiu, hic⟩ := hi
    apply lt_of_le_of_ne (hc i hiu)
    -- from the assumption that `v x` is not the n-th root of any `v (algebraMap K A r)`,
    -- we can derive that the `v (p.coeff i • x ^ i)` are all distinct
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_pow, map_pow]
    clear hc
    wlog hci : c < i generalizing i c with ih
    · exact (ih i hiu c hcu hic.symm ((lt_trichotomy i c).resolve_right (·.elim hic hci))).symm
    intro h
    apply hne (i - c) (p.coeff c / p.coeff i) (Nat.sub_ne_zero_of_lt hci)
    rw [pow_sub₀ (v x) hx0 hci.le, ← comap_apply, map_div₀, comap_apply, comap_apply,
      ← div_eq_mul_inv, div_eq_div_iff (pow_ne_zero c hx0) (hi0 i hiu), ← h, mul_comm]
  -- hence `v (p.aeval x) = v (p.coeff c • x ^ c) ≠ 0`, however `v (p.aeval x) = v 0 = 0`
  rw [v.map_sum_eq_of_lt hcu hc, Algebra.smul_def, map_mul, map_pow]
  exact mul_ne_zero (hi0 c hcu) (pow_ne_zero c hx0)

end Valuation
