/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Triviality of power-multiplicative norms

In this file, we prove triviality of power-multiplicative norms over trivially normed fields.

## Main Results

* `AlgebraNorm.eq_one_of_trivial` : a power-multiplicative norm on an integral extension of a
  trivially normed field is trivial.
-/

section Ring

variable {A B : Type*} [SeminormedCommRing A] [Ring B] [Algebra A B]

/-- A power-multiplicative norm on an algebraic extension of a trivially normed field is trivial. -/
theorem AlgebraNorm.le_one_of_trivial (hK : ∀ x : A, ‖x‖ ≤ 1)
    (f : AlgebraNorm A B) (hf : IsPowMul f) (x : B) (hx : IsIntegral A x) : f x ≤ 1 := by
  let S := Algebra.adjoin A {x}
  obtain ⟨s, hs⟩ : S.toSubmodule.FG := hx.fg_adjoin_singleton
  have h n (hn : 1 ≤ n) : f x ^ n ≤ ∑ a : s, f a := by
    obtain ⟨c, hc⟩ : ∃ c : s → A, ∑ a : s, c a • a.val = x ^ n := by
      rw [← Submodule.mem_span_finset', hs]
      exact S.pow_mem (Algebra.self_mem_adjoin_singleton A x) n
    grw [← hf x hn, ← hc, Finset.map_sum_le_sum]
    gcongr
    grw [map_smul_eq_mul, hK, one_mul]
  contrapose! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ a : s, f a) h
  by_cases! hn0 : n = 0
  · exact ⟨1, le_rfl, by grw [pow_one, hn, hn0, pow_zero, h]⟩
  · exact ⟨n, hn0.pos, hn⟩

end Ring

section Field

variable {K L : Type*} [SeminormedCommRing K] [DivisionRing L] [Algebra K L]
  [Algebra.IsIntegral K L]

/-- A power-multiplicative norm on an integral extension of a trivially normed field is trivial. -/
theorem AlgebraNorm.eq_one_of_trivial
    (hK : ∀ x : K, ‖x‖ ≤ 1) (f : AlgebraNorm K L) (hf : IsPowMul f)
    (x : L) (hx : x ≠ 0) : f x = 1 := by
  refine le_antisymm (AlgebraNorm.le_one_of_trivial hK f hf x (Algebra.IsIntegral.isIntegral x)) ?_
  grw [one_le_map_one f, ← inv_mul_cancel₀ hx, map_mul_le_mul, f.le_one_of_trivial hK hf, one_mul]
  exact Algebra.IsIntegral.isIntegral x⁻¹

end Field
