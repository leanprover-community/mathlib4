/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-!
# Sqrt extension for tactic `dyadic_interval`

This file implements sqrt extension for the tactic `dyadic_interval` using `Nat.sqrt`
-/

@[expose] public section

namespace Inclusion

/-- Square root of an interval. -/
def Interval.sqrt (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := match I.lb with
    | ⊥ => WithBot.some 0
    | WithBot.some lb =>
      if 0 ≤ lb.toRat then Dyadic.ofIntWithPrec ⌊lb.toRat * 4 ^ prec⌋.toNat.sqrt prec
      else WithBot.some 0
  ub := match I.ub with
    | ⊤ => ⊤
    | WithTop.some ub =>
      let ub' : ℕ := ⌈ub.toRat * 4 ^ prec⌉.toNat
      let ubsqrt : ℕ := ub'.sqrt
      if ub' ≤ ubsqrt ^ 2 then Dyadic.ofIntWithPrec ubsqrt prec
      else Dyadic.ofIntWithPrec (ubsqrt + 1) prec

open Dyadic in
theorem Interval.sqrt_mem
    (f : Dyadic ↪o ℝ) (map_zero : f 0 = 0) (map_sq : ∀ x, f (x ^ 2) = f x ^ 2)
    {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I.map f) (prec : ℕ) :
    √x ∈ (I.sqrt prec).map f := by
  have H (n : ℤ) (q : Dyadic) :
      (f q ≤ f (.ofIntWithPrec n prec) ^ 2 ↔ q.toRat * 4 ^ prec ≤ n ^ 2) ∧
      (f (.ofIntWithPrec n prec) ^ 2 ≤ f q ↔ n ^ 2 ≤ q.toRat * 4 ^ prec) := by
    norm_num [← map_sq, ← toRat_le_toRat_iff, toRat_ofIntWithPrec_eq_mul_two_pow, mul_pow,
      le_mul_inv_iff₀, mul_inv_le_iff₀, ← pow_mul, pow_mul']
  have hub (n : ℕ) (q : Dyadic) (hq : x ≤ f q) (h : ⌈q.toRat * 4 ^ prec⌉.toNat ≤ n ^ 2) :
      √x ≤ f (.ofIntWithPrec n prec) := by
    rw [Int.ceil_toNat, Nat.ceil_le] at h
    refine Real.sqrt_le_iff.mpr ⟨map_zero ▸ f.monotone ?_, hq.trans ((H n q).left.mpr (mod_cast h))⟩
    simp [← toRat_le_toRat_iff, toRat_ofIntWithPrec_eq_mul_two_pow, toRat_zero]
  obtain ⟨hl, hu⟩ := (mem_map_iff f).mp hx
  refine (mem_map_iff f).mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rcases I with ⟨_ | lb, ub⟩ <;> simp only [Interval.sqrt] at ha
    · simp [map_zero, ← WithBot.coe_eq_coe.mp ha]
    · split_ifs at ha with h0
      · cases ha
        refine Real.le_sqrt_of_sq_le (((H _ lb).right.mpr ?_).trans (hl lb rfl))
        have h := ⌊lb.toRat * 4 ^ prec⌋.toNat.sqrt_le'
        rw [Int.floor_toNat, Nat.le_floor_iff (mul_nonneg h0 (by simp))] at h
        exact_mod_cast h
      · simp [map_zero, ← WithBot.coe_eq_coe.mp ha]
  · rcases I with ⟨lb, _ | ub⟩ <;> simp only [Interval.sqrt] at ha
    · cases ha
    · split_ifs at ha with h1 <;> cases ha
      · exact hub _ ub (hu ub rfl) h1
      · exact_mod_cast hub _ ub (hu ub rfl) (Nat.lt_succ_sqrt' _).le

@[inclusion_op interval_dyadic_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (prec : ℕ) (hx : x ∈ I) : √x ∈ I.sqrt prec :=
  Interval.sqrt_mem Dyadic.toRealOrderEmbedding (map_zero Dyadic.toRealAddMonoidHom)
    (Dyadic.toReal_pow (n := 2)) hx prec

end Inclusion
