/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Data.Real.Sqrt

/-! # `norm_num` extension for `Real.sqrt`

This module defines a `norm_num` extension for `Real.sqrt` and `NNReal.sqrt`.
-/

namespace Tactic.NormNum

open Qq Lean Lean.Meta Elab.Tactic Mathlib.Meta.NormNum NNReal

lemma isNat_realSqrt {x : ℝ} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat √x ny := ⟨by simp [h.out, ← hy]⟩

lemma isNat_nnrealSqrt {x : ℝ≥0} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (NNReal.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩

lemma isNNRat_nnrealSqrt_of_isNNRat {x : ℝ≥0} {n sn : ℕ} {d sd : ℕ} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat (NNReal.sqrt x) sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero, ← Nat.cast_mul, hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, NNReal.sqrt_mul]

lemma isNat_realSqrt_neg {x : ℝ} {nx : ℕ} (h : IsInt x (Int.negOfNat nx)) :
    IsNat √x (nat_lit 0) := ⟨by simp [Real.sqrt_eq_zero', h.out]⟩

lemma isNat_realSqrt_of_isRat_negOfNat {x : ℝ} {num : ℕ} {denom : ℕ}
    (h : IsRat x (.negOfNat num) denom) : IsNat √x (nat_lit 0) := by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  have h₁ : 0 ≤ (num : ℚ) * ⅟(denom : ℝ) :=
    mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)
  simpa [Nat.cast_zero, Real.sqrt_eq_zero', Int.cast_negOfNat, neg_mul, neg_nonpos] using h₁

lemma isNNRat_realSqrt_of_isNNRat {x : ℝ} {n sn : ℕ} {d sd : ℕ} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsNNRat x n d) :
    IsNNRat √x sn sd := by
  obtain ⟨_, rfl⟩ := h
  refine ⟨?_, ?out⟩
  · apply invertibleOfNonzero
    rw [← mul_self_ne_zero, ← Nat.cast_mul, hd]
    exact Invertible.ne_zero _
  · simp [← hn, ← hd, Real.sqrt_mul (mul_self_nonneg ↑sn)]

/-- `norm_num` extension that evaluates the function `Real.sqrt`. -/
@[norm_num √_]
def evalRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(√$x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sℝ ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat q($sℝ) q($ey) q(isNat_realSqrt $pf $pf₁)
    | .isNegNat _ ex pf =>
        -- Recall that `Real.sqrt` returns 0 for negative inputs
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_neg $pf)
    | .isNegNNRat sℝ eq n ed pf =>
        assumeInstancesCommute
        return .isNat q(inferInstance) q(nat_lit 0) q(isNat_realSqrt_of_isRat_negOfNat $pf)
    | .isNNRat sℝ eq n' ed pf =>
          let n : ℕ := n'.natLit!
          let d : ℕ := ed.natLit!
          let sn := Nat.sqrt n
          let sd := Nat.sqrt d
          unless sn * sn = n ∧ sd * sd = d do failure
          have esn : Q(ℕ) := mkRawNatLit sn
          have esd : Q(ℕ) := mkRawNatLit sd
          have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
          have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
          assumeInstancesCommute
          -- will never be an integer
          return .isNNRat q($sℝ) (sn / sd) _ q($esd) q(isNNRat_realSqrt_of_isNNRat $hn $hd $pf)
  | _ => failure

/-- `norm_num` extension that evaluates the function `NNReal.sqrt`. -/
@[norm_num NNReal.sqrt _]
def evalNNRealSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    match ← derive x with
    | .isBool _ _ => failure
    | .isNat sℝ ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        unless y * y = x do failure
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat sℝ ey q(isNat_nnrealSqrt $pf $pf₁)
    | .isNegNat _ ex pf => failure
    | .isNNRat sℝ eq n' ed pf =>
        let n : ℕ := n'.natLit!
        let d : ℕ := ed.natLit!
        let sn := Nat.sqrt n
        let sd := Nat.sqrt d
        unless sn * sn = n ∧ sd * sd = d do failure
        have esn : Q(ℕ) := mkRawNatLit sn
        have esd : Q(ℕ) := mkRawNatLit sd
        have hn : Q($esn * $esn = $n') := (q(Eq.refl $n') : Expr)
        have hd : Q($esd * $esd = $ed) := (q(Eq.refl $ed) : Expr)
        assumeInstancesCommute
        -- will never be an integer
        return .isNNRat q($sℝ) (sn / sd) _ q($esd) q(isNNRat_nnrealSqrt_of_isNNRat $hn $hd $pf)
    | .isNegNNRat sℝ eq en ed pf => failure
  | _ => failure

end Tactic.NormNum
