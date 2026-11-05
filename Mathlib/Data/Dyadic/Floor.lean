/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Dyadic
public import Mathlib.Data.Rat.Floor

/-!
# Floor and ceil of dyadic rationals

This file defines integer floor and ceil for dyadic rationals using bit shifts and provides a
`FloorRing Dyadic` instance using these operations.
-/

@[expose] public section

namespace Dyadic

/-- Round a dyadic rational down to an integer. -/
def intFloor : Dyadic → ℤ
  | .zero => 0
  | .ofOdd n (.ofNat k) _ => n >>> k
  | .ofOdd n (.negSucc k) _ => n <<< (k + 1)

/-- Round a dyadic rational up to an integer. -/
def intCeil : Dyadic → ℤ
  | .zero => 0
  | .ofOdd n (.ofNat 0) _ => n
  | .ofOdd n (.ofNat (k + 1)) _ => (n >>> (k + 1)) + 1
  | .ofOdd n (.negSucc k) _ => n <<< (k + 1)

@[simp]
theorem intFloor_toRat (x : Dyadic) : ⌊x.toRat⌋ = x.intFloor := by
  cases x with
  | zero => simp [intFloor]
  | ofOdd n k hn =>
    cases k with
    | ofNat k => simp [intFloor, toRat, Rat.floor_def', Int.shiftRight_eq_div_pow]
    | negSucc k =>
      rw [intFloor, toRat, Int.floor_intCast]
      simp [Int.shiftLeft_eq]

@[simp]
theorem intCeil_toRat (x : Dyadic) : ⌈x.toRat⌉ = x.intCeil := by
  cases x with
  | zero => simp [intCeil]
  | ofOdd n k hn =>
    rcases k with (_ | k) | k
    · simp [intCeil, toRat]
    · rw [(Int.ceil_eq_floor_add_one_iff_notMem _).mpr ?_, intFloor_toRat]
      · rfl
      · rintro ⟨z, hz⟩
        have := congrArg Rat.den hz.symm
        simp [toRat] at this
    · rw [intCeil, toRat, Int.ceil_intCast]
      simp [Int.shiftLeft_eq]

instance : FloorRing Dyadic where
  floor := intFloor
  ceil := intCeil
  gc_coe_floor z x := by
    rw [← toRat_le_toRat_iff, toRat_intCast, ← Int.le_floor, intFloor_toRat]
  gc_ceil_coe x z := by
    rw [← toRat_le_toRat_iff, toRat_intCast, ← Int.ceil_le, intCeil_toRat]

@[simp]
theorem intFloor_toReal (x : Dyadic) : ⌊x.toReal⌋ = x.intFloor := by
  simp [toReal]

@[simp]
theorem intCeil_toReal (x : Dyadic) : ⌈x.toReal⌉ = x.intCeil := by
  simp [toReal]

end Dyadic
