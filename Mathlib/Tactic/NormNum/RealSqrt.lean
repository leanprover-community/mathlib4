/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Data.Real.Sqrt

/-! # `norm_num` extension for `Real.sqrt`

This module defines a `norm_num` extension for `Real.sqrt` and `NNReal.sqrt`.

## Implementation notes

While the extension for `Real.sqrt` can handle both integers and rationals, the one for
`NNReal.sqrt` can only deal with integers, due to a limitation of norm_num
(i.e. the `IsRat` type requires a Ring instance).
-/

namespace Tactic.NormNum

open Qq Lean Lean.Meta Elab.Tactic Mathlib.Meta.NormNum NNReal

lemma isNat_realSqrt {x : ℝ} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat √x ny := ⟨by simp [h.out, ← hy]⟩

lemma isNat_nnrealSqrt {x : ℝ≥0} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (NNReal.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩

lemma isNat_realSqrt_neg {x : ℝ} {nx : ℕ} (h : IsInt x (Int.negOfNat nx)) :
    IsNat √x 0 := by
  refine ⟨?_⟩
  simp only [Nat.cast_zero]
  refine Real.sqrt_eq_zero_of_nonpos ?_
  simp [h.out]

lemma isNat_realSqrt_of_isRat_negOfNat {x : ℝ} {num : ℕ} {denom : ℕ}
    (h : IsRat x (.negOfNat num) denom) : IsNat √x 0 := by
  refine ⟨?_⟩
  obtain ⟨inv, rfl⟩ := h
  simp only [Nat.cast_zero]
  refine Real.sqrt_eq_zero_of_nonpos ?_
  simp only [Int.cast_negOfNat, neg_mul, neg_nonpos]
  exact mul_nonneg (Nat.cast_nonneg' _) (invOf_nonneg.2 <| Nat.cast_nonneg' _)

lemma isRat_realSqrt_of_isRat_ofNat {x : ℝ} {n sn : ℕ} {d sd : ℕ} (hn : sn * sn = n)
    (hd : sd * sd = d) (h : IsRat x (.ofNat n) d) :
    IsRat √x (.ofNat sn) sd := by
  obtain ⟨inv, rfl⟩ := h
  obtain rfl | hd₂ := eq_or_ne sd 0
  · simp at hd
    subst hd
    refine ⟨inv, ?_⟩
    simp
  refine ⟨invertibleOfNonzero (by exact_mod_cast hd₂), ?out⟩
  rw [← hn, invOf_eq_inv, ← hd]
  simp only [Int.ofNat_eq_coe, Int.cast_mul, Nat.cast_mul, mul_inv_rev, invOf_eq_inv,
    Int.cast_natCast]
  rw [Real.sqrt_mul (mul_self_nonneg ↑sn)]
  aesop

/-- `norm_num` extension that evaluates the function `Real.sqrt`. -/
@[norm_num √_]
def evalRealSqrt : NormNumExt where eval {u α} e := do
  let .app _ (x : Q(ℝ)) ← whnfR e | failure
  have : u =QL 0 := ⟨⟩; have : $α =Q ℝ := ⟨⟩; have : $e =Q √$x := ⟨⟩
  match ← derive x with
  | .isBool _ _ => failure
  | .isNat sℝ ex pf =>
      let x := ex.natLit!
      let y := Nat.sqrt x
      if y * y = x then
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        return .isNat sℝ ey q(isNat_realSqrt $pf $pf₁)
      else failure
  | .isNegNat _ ex pf =>
      -- Recall that `Real.sqrt` returns 0 for negative inputs
      assumeInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(isNat_realSqrt_neg $pf)
  | .isRat sℝ eq en ed pf =>
      match en with
      | .app (.const ``Int.negOfNat []) (n : Q(ℕ)) =>
        have : (Int.negOfNat $n) =Q $en := ⟨⟩
        assumeInstancesCommute
        return .isNat q(inferInstance) (mkRawNatLit 0) q(isNat_realSqrt_of_isRat_negOfNat $pf)
      | .app (.const ``Int.ofNat []) (n' : Q(ℕ)) =>
        have : Int.ofNat $n' =Q $en := ⟨⟩
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
        return .isRat sℝ (sn / sd) _ esd q(isRat_realSqrt_of_isRat_ofNat $hn $hd $pf)
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
        if y * y = x then
          have ey : Q(ℕ) := mkRawNatLit y
          have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
          assumeInstancesCommute
          return .isNat sℝ ey q(isNat_nnrealSqrt $pf $pf₁)
        else failure
    | .isNegNat _ ex pf => failure
    | .isRat sℝ eq en ed pf =>
        -- `IsRat` only works on types with a `Ring` instance, so it can't work on `ℝ≥0`.
        failure
  | _ => failure

end Tactic.NormNum
