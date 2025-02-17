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

open Qq Lean Lean.Meta Elab.Tactic Mathlib.Meta.NormNum

lemma isNat_realSqrt {x : ℝ} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (Real.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩

lemma isNat_nnrealSqrt {x : ℝ≥0} {nx ny : ℕ} (h : IsNat x nx) (hy : ny * ny = nx) :
    IsNat (NNReal.sqrt x) ny := ⟨by simp [h.out, ← hy]⟩

lemma isNat_realSqrt_neg {x : ℝ} {nx : ℕ} (h : IsInt x (Int.negOfNat nx)) :
    IsNat (Real.sqrt x) 0 := by
  refine ⟨?_⟩
  simp only [Nat.cast_zero]
  refine Real.sqrt_eq_zero_of_nonpos ?_
  simp [h.out]

lemma isNat_realSqrt_neg_of_isRat {x : ℝ} {num : ℤ} {denom : ℕ} (hnum : num ≤ 0)
    (h : IsRat x num denom) : IsNat (Real.sqrt x) 0 := by
  refine ⟨?_⟩
  simp only [Nat.cast_zero]
  refine Real.sqrt_eq_zero_of_nonpos ?_
  let .mk inv eq := h
  simp only [eq]
  refine mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hnum) ?_
  rw [invOf_nonneg]
  exact Nat.cast_nonneg' denom

lemma isRat_realSqrt {x : ℝ} {n sn : ℤ} {d sd : ℕ} (hn : sn * sn = n)
    (hn₂ : 0 ≤ sn) (hd : sd * sd = d) (hd₂ : sd ≠ 0) (h : IsRat x n d) :
    IsRat (Real.sqrt x) sn sd := by
  refine .mk (invertibleOfNonzero (by exact_mod_cast hd₂)) ?out
  let .mk inv eq := h
  rw [eq, ← hn, invOf_eq_inv, ← hd]
  simp only [Int.cast_mul, Nat.cast_mul, mul_inv_rev, invOf_eq_inv]
  rw [Real.sqrt_mul (mul_self_nonneg ↑sn)]
  aesop

/-- `norm_num` extension that evaluates the function `Real.sqrt`. -/
@[norm_num Real.sqrt _]
def evalRealSqrt : NormNumExt where eval {_ _} e := do
  let .app _ (x : Q(ℝ)) ← whnfR e | failure
  let res ← derive (α := q(ℝ)) x
  match res with
  | .isBool _ _ => failure
  | .isNat sℝ ex pf =>
      let x := ex.natLit!
      let y := Nat.sqrt x
      if y * y = x then
        have ey : Q(ℕ) := mkRawNatLit y
        have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
        assumeInstancesCommute
        have pf_final : Q(IsNat (Real.sqrt $x) $ey) := q(isNat_realSqrt $pf $pf₁)
        return .isNat sℝ ey pf_final
      else failure
  | .isNegNat _ ex pf =>
      -- Recall that `Real.sqrt` returns 0 for negative inputs
      assumeInstancesCommute
      have pf_final : Q(IsNat (Real.sqrt $x) 0) := q(isNat_realSqrt_neg $pf)
      let sℝ : Q(AddMonoidWithOne ℝ) ← synthInstanceQ q(AddMonoidWithOne ℝ)
      return .isNat sℝ (mkRawNatLit 0) pf_final
  | .isRat sℝ eq en ed pf =>
      let n' : ℤ := en.intLit!
      let d : ℕ := ed.natLit!
      if n' ≤ 0 then
        -- Square root of a negative number, defined to be zero
        let hnum : Q($en ≤ 0) ← mkDecideProof q($en ≤ 0)
        assumeInstancesCommute
        have pf_final : Q(IsNat (Real.sqrt $x) 0) := q(isNat_realSqrt_neg_of_isRat $hnum $pf)
        let sℝ : Q(AddMonoidWithOne ℝ) ← synthInstanceQ q(AddMonoidWithOne ℝ)
        return .isNat sℝ (mkRawNatLit 0) pf_final
      let n : ℕ := n'.toNat
      let sn : ℤ := Nat.sqrt n
      let sd := Nat.sqrt d
      if sn * sn = n ∧ sd * sd = d then
        have esn : Q(ℤ) := mkRawIntLit sn
        have esd : Q(ℕ) := mkRawNatLit sd
        let hn : Q($esn * $esn = $en) ← mkDecideProof q($esn * $esn = $en)
        let hn₂ : Q(0 ≤ $esn) ← mkDecideProof q(0 ≤ $esn)
        let hd : Q($esd * $esd = $ed) ← mkDecideProof q($esd * $esd = $ed)
        let hd₂ : Q($esd ≠ 0) ← mkDecideProof q($esd ≠ 0)
        assumeInstancesCommute
        have pf_final : Q(IsRat (Real.sqrt $x) $esn $esd) :=
          q(isRat_realSqrt $hn $hn₂ $hd $hd₂ $pf)
        return .isRat sℝ (sn / sd) esn esd pf_final
      else failure

/-- `norm_num` extension that evaluates the function `NNReal.sqrt`. -/
@[norm_num NNReal.sqrt _]
def evalNNRealSqrt : NormNumExt where eval {u α} e := do
  let e' : Q(«$α») ← whnfR e
  match u, α, e' with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $x) =>
    let res ← derive (α := q(ℝ≥0)) x
    match res with
    | .isBool _ _ => failure
    | .isNat sℝ ex pf =>
        let x := ex.natLit!
        let y := Nat.sqrt x
        if y * y = x then
          have ey : Q(ℕ) := mkRawNatLit y
          have pf₁ : Q($ey * $ey = $ex) := (q(Eq.refl $ex) : Expr)
          assumeInstancesCommute
          have pf_final : Q(IsNat (NNReal.sqrt $x) $ey) := q(isNat_nnrealSqrt $pf $pf₁)
          return .isNat sℝ ey pf_final
        else failure
    | .isNegNat _ ex pf => failure
    | .isRat sℝ eq en ed pf =>
        -- `IsRat` only works on types with a `Ring` instance, so it can't work on `ℝ≥0`.
        failure
  | _ => failure

end Tactic.NormNum
