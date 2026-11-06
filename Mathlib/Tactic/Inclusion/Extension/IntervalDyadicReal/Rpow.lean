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

open Real

namespace Inclusion

namespace IntervalDyadicReal

/-- Computes an enclosure of `log x` at precision `prec` for `x ∈ I` with `0 < x`. -/
@[expose]
def logPos (I : Interval Dyadic) (prec : ℕ) : Interval Dyadic where
  lb := if 0 < I.lb then I.lb.map (lowerLog · prec) else ⊥
  ub := I.ub.map (upperLog · prec)

theorem log_mem_logPos {x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ I) (hx₀ : 0 < x) (prec : ℕ) :
    x.log ∈ logPos I prec := by
  obtain ⟨hxl, hxu⟩ := (Interval.mem_map_iff Dyadic.toReal).mp (mem_iff_mem_map.mp hx)
  rw [logPos]
  refine mem_iff_mem_map.mpr <| Interval.mem_map_iff Dyadic.toReal |>.mpr
    ⟨fun lb hlb => ?_, fun ub hub => ?_⟩
  · by_cases hl : 0 < I.lb
    · rw [ite_eq_left hl, WithBot.map_eq_some_iff] at hlb
      obtain ⟨lb, hlb, rfl⟩ : ∃ lb' : Dyadic, I.lb = lb' ∧ lowerLog lb' prec = lb := hlb
      have hlb₀ : 0 < Dyadic.toReal lb := by
        rw [← Dyadic.toReal_zero, Dyadic.toReal_lt_toReal]
        aesop
      simpa [Dyadic.toReal] using lowerLog_le lb prec |>.trans (log_le_log hlb₀ (hxl lb hlb))
    · rw [ite_eq_right hl] at hlb
      cases hlb
  · rw [WithTop.map_eq_some_iff] at hub
    obtain ⟨ub, hub, rfl⟩ : ∃ ub' : Dyadic, I.ub = ub' ∧ upperLog ub' prec = ub := hub
    simpa [Dyadic.toReal] using log_le_log hx₀ (hxu ub hub) |>.trans <| le_upperLog ub prec

/-- Reserved for an enclosure of `x ^ y` for `x < 0`. -/
@[expose]
def negRpow (_I _J : Interval Dyadic) (_prec : ℕ) : Interval Dyadic := .univ Dyadic

/-- Computes an enclosure of `(0 : ℝ) ^ y` for `y ∈ J`. -/
@[expose]
def zeroRpow (J : Interval Dyadic) : Interval Dyadic :=
  if J.lb = 0 ∧ J.ub = 0 then
    .singleton 1
  else if 0 < J.lb ∨ J.ub < 0 then
    .singleton 0
  else
    .Icc 0 1

/-- Computes an enclosure of `x ^ y` at precision `prec` for `x ∈ I` with `0 < x`. -/
@[expose]
def posRpow (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  let wp : ℕ := prec + 1 + max
    (match J.lb with | some (.ofOdd n p _) => (n.natAbs.log2 - p + 1).toNat | _ => 0)
    (match J.ub with | some (.ofOdd n p _) => (n.natAbs.log2 - p + 1).toNat | _ => 0)
  exp (logPos I wp |>.mul J) (prec + 1)

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
    x ^ y ∈ negRpow I J prec := Interval.mem_map_univ Dyadic.toReal _

theorem rpow_mem_zeroRpow {y : ℝ} {J : Interval Dyadic} (hy : y ∈ J) :
    0 ^ y ∈ zeroRpow J := by
  by_cases hJ1 : J.lb = 0 ∧ J.ub = 0
  · have hy : WithBot.some (Dyadic.toReal 0) ≤ y ∧ y ≤ WithTop.some (Dyadic.toReal 0) :=
      ⟨hy.left.trans_eq' <| congrArg (WithBot.map Dyadic.toReal) hJ1.left,
        hy.right.trans_eq <| congrArg (WithTop.map Dyadic.toReal) hJ1.right⟩
    cases le_antisymm (a := 0) (b := y) (by simpa using hy.left) (by simpa using hy.right)
    simp only [zeroRpow, hJ1, and_self, ↓reduceIte]
    rw [rpow_zero, ← Rat.cast_one, ← Dyadic.toRat_one]
    exact Interval.mem_map_singleton 1 Dyadic.toReal
  by_cases hJ2 : 0 < J.lb ∨ J.ub < 0
  · simp only [zeroRpow, hJ1, hJ2, ↓reduceIte]
    rcases hJ2 with hJ2 | hJ2 <;> [
      have : WithBot.some (Dyadic.toReal 0) < y :=
        hy.left.trans_lt' <| Dyadic.toRealOrderEmbedding.withBotMap.lt_iff_lt.mpr hJ2;
      have : y < WithTop.some (Dyadic.toReal 0) :=
        hy.right.trans_lt <| Dyadic.toRealOrderEmbedding.withTopMap.lt_iff_lt.mpr hJ2] <;>
      rw [zero_rpow (by simp at this; grind), ← Dyadic.toReal_zero] <;>
      exact Interval.mem_map_singleton 0 Dyadic.toReal
  · simp only [zeroRpow, hJ1, hJ2, ↓reduceIte]
    apply Interval.mem_map_Icc
    · simpa using zero_rpow_nonneg y
    · simpa [Dyadic.toReal] using zero_rpow_le_one y

theorem rpow_mem_posRpow {x y : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ I) (hx₀ : 0 < x) (hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ posRpow I J prec := by
  rw [rpow_def_of_pos hx₀]
  exact exp_mem (mul_mem (log_mem_logPos hx hx₀ _) hy) _

@[inclusion_op interval_dyadic_real]
theorem rpow_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ rpow I J prec := by
  rcases lt_trichotomy I.ub 0 with hIub | hIub | hIub
  · simp only [rpow, hIub, ↓reduceIte]
    have : x < WithTop.some (Dyadic.toReal 0) :=
      hx.right.trans_lt <| Dyadic.toRealOrderEmbedding.withTopMap.lt_iff_lt.mpr hIub
    exact rpow_mem_negRpow hx (by simpa) hy prec
  · simp only [rpow, hIub, lt_self_iff_false, ↓reduceIte]
    have hx₀' : x ≤ WithTop.some (Dyadic.toReal 0) :=
      hx.right.trans_eq <| congrArg (WithTop.map Dyadic.toReal) hIub
    simp only [Dyadic.toReal_zero, WithTop.coe_zero, WithTop.coe_le_zero] at hx₀'
    rcases lt_trichotomy I.lb 0 with hIlb | hIlb | hIlb
    · simp only [hIlb, ↓reduceIte]
      rcases eq_or_lt_of_le (by simpa) with rfl | hx₀
      · exact Interval.hull_mem_right Dyadic.toRealOrderEmbedding <| rpow_mem_zeroRpow hy
      · exact Interval.hull_mem_left Dyadic.toRealOrderEmbedding <| rpow_mem_negRpow hx hx₀ hy prec
    · simp only [hIlb, lt_self_iff_false, ↓reduceIte]
      have : WithBot.some (Dyadic.toReal 0) ≤ x :=
        hx.left.trans_eq' <| congrArg (WithTop.map Dyadic.toReal) hIlb
      exact le_antisymm (by simpa) hx₀' ▸ rpow_mem_zeroRpow hy
    · simp only [hIlb.not_gt, ↓reduceIte]
      have : WithBot.some (Dyadic.toReal 0) < x :=
        hx.left.trans_lt' <| Dyadic.toRealOrderEmbedding.withBotMap.lt_iff_lt.mpr hIlb
      simp [hx₀'.not_gt] at this
  · simp only [rpow, hIub.not_gt, hIub.ne', ↓reduceIte]
    rcases lt_trichotomy I.lb 0 with hIlb | hIlb | hIlb
    · simp only [hIlb, ↓reduceIte]
      rcases lt_trichotomy x 0 with hx₀ | rfl | hx₀
      · exact Interval.hull_mem_left Dyadic.toRealOrderEmbedding <|
          Interval.hull_mem_left Dyadic.toRealOrderEmbedding <| rpow_mem_negRpow hx hx₀ hy prec
      · exact Interval.hull_mem_left Dyadic.toRealOrderEmbedding <|
          Interval.hull_mem_right Dyadic.toRealOrderEmbedding <| rpow_mem_zeroRpow hy
      · refine Interval.hull_mem_right Dyadic.toRealOrderEmbedding <|
          rpow_mem_posRpow ?_ (by simpa) hy prec
        apply Interval.inter_mem Dyadic.toRealOrderEmbedding hx ⟨?_, le_top⟩
        change WithBot.map Dyadic.toReal 0 ≤ x
        simpa using hx₀.le
    · simp only [hIlb, lt_self_iff_false, ↓reduceIte]
      have : WithBot.some (Dyadic.toReal 0) ≤ x :=
        hx.left.trans_eq' <| congrArg (WithTop.map Dyadic.toReal) hIlb
      rcases eq_or_lt_of_le (by simpa) with rfl | hx₀
      · exact Interval.hull_mem_left Dyadic.toRealOrderEmbedding <| rpow_mem_zeroRpow hy
      · exact Interval.hull_mem_right Dyadic.toRealOrderEmbedding <|
          rpow_mem_posRpow hx (by simpa) hy prec
    · simp only [hIlb.not_gt, hIlb.ne', ↓reduceIte]
      have : WithBot.some (Dyadic.toReal 0) < x :=
        hx.left.trans_lt' <| Dyadic.toRealOrderEmbedding.withBotMap.lt_iff_lt.mpr hIlb
      exact rpow_mem_posRpow hx (by simpa) hy prec

end IntervalDyadicReal

end Inclusion
