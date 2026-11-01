/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

/-!
# `Real.rpow` extension for tactic `dyadic_interval`

This file implements `Real.rpow` extension for the tactic `dyadic_interval`.
-/

public section

attribute [local grind unfold] WithBot.some WithTop.some
attribute [local grind norm ←] WithBot.coe_zero WithTop.coe_zero
  WithBot.none_eq_bot WithTop.none_eq_top
attribute [local grind norm] WithBot.coe_le_coe WithTop.coe_le_coe
attribute [local grind =] WithBot.coe_le_iff WithTop.le_coe_iff

local grind_pattern OrderEmbedding.le_iff_le => a ≤ b, f a, f b

namespace Inclusion

namespace IntervalDyadicReal

/-- TODO doc -/
def logPos (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  sorry

theorem log_mem_logPos {x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ I) (hx₀ : 0 < x) (prec : ℕ) :
    x.log ∈ logPos I prec := by
  sorry

/-- TODO doc -/
@[expose]
def negRpow (_I _J : Interval Dyadic) (_prec : ℕ) : Interval Dyadic := .univ Dyadic

/-- TODO doc -/
@[expose]
def zeroRpow (J : Interval Dyadic) : Interval Dyadic :=
  if J.lb = 0 ∧ J.ub = 0 then
    .singleton 1
  else if 0 < J.lb ∨ J.ub < 0 then
    .singleton 0
  else
    .Icc 0 1

/-- TODO doc -/
@[expose]
def posRpow (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let wp : ℕ := prec + 1024
  exp (logPos I wp |>.mul J) prec

/-- Computes an enclosure of `x ^ y` for `x ∈ I` and `y ∈ J` with precision `prec`. -/
@[expose]
def rpow (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  if I.ub < 0 then
    negRpow I J prec
  else if I.ub = 0 then
    if I.lb < 0 then
      negRpow I J prec |>.hull <| zeroRpow J
    else
      zeroRpow J
  else
    if I.lb < 0 then
      negRpow (I.inter <| .Iic 0) J prec |>.hull (zeroRpow J) |>.hull <|
        posRpow (I.inter <| .Ici 0) J prec
    else if I.lb = 0 then
      zeroRpow J |>.hull <| posRpow I J prec
    else
      posRpow I J prec

theorem rpow_mem_negRpow {x y : ℝ} {I J : Interval Dyadic}
    (_hx : x ∈ I) (_hx₀ : x < 0) (_hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ negRpow (I.inter <| .Iic 0) J prec := Interval.mem_map_univ Dyadic.toReal _

theorem rpow_mem_zeroRpow {y : ℝ} {J : Interval Dyadic} (hy : y ∈ J) :
    0 ^ y ∈ zeroRpow J := by
  sorry

theorem rpow_mem_posRpow {x y : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ I) (hx₀ : 0 < x) (hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ posRpow I J prec := by
  rw [Real.rpow_def_of_pos hx₀]
  exact exp_mem (mul_mem (log_mem_logPos hx hx₀ _) hy) _

@[inclusion_op interval_dyadic_real]
theorem rpow_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ rpow I J prec := by
  -- apply Interval.mem_map_iff Dyadic.toReal |>.mp at hx
  -- apply Interval.mem_map_iff Dyadic.toReal |>.mp at hy
  rcases lt_trichotomy I.ub 0 with hIub | hIub | hIub
  · simp only [rpow, hIub, ↓reduceIte]
    have : x < WithTop.some (Dyadic.toReal 0) :=
      hx.right.trans_lt <| Dyadic.toRealOrderEmbedding.withTopMap.lt_iff_lt.mpr hIub
    exact rpow_mem_negRpow hx (by simpa) hy prec
  · simp only [rpow, hIub, lt_self_iff_false, ↓reduceIte]
    rcases lt_trichotomy I.lb 0 with hIlb | hIlb | hIlb
    · simp only [hIlb, ↓reduceIte]
      sorry
    · simp only [hIlb, lt_self_iff_false, ↓reduceIte]
      sorry
    · simp only [hIlb.not_gt, ↓reduceIte]
      -- contradiction
      sorry
  · simp only [rpow, hIub.not_gt, hIub.ne', ↓reduceIte]
    rcases lt_trichotomy I.lb 0 with hIlb | hIlb | hIlb
    · simp only [hIlb, ↓reduceIte]
      sorry
    · simp only [hIlb, lt_self_iff_false, ↓reduceIte]
      sorry
    · simp only [hIlb.not_gt, hIlb.ne', ↓reduceIte]
      sorry

end IntervalDyadicReal

end Inclusion
