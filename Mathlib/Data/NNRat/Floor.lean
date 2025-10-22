/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Rat.Floor

/-!
# Floor Function for Non-negative Rational Numbers

## Summary

We define the `FloorSemiring` instance on `ℚ≥0`, and relate its operators to `NNRat.cast`.

Note that we cannot talk about `Int.fract`, which currently only works for rings.

## Tags

nnrat, rationals, ℚ≥0, floor
-/

assert_not_exists Finset

namespace NNRat

instance : FloorSemiring ℚ≥0 where
  floor q := ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]
theorem floor_coe (q : ℚ≥0) : ⌊(q : ℚ)⌋₊ = ⌊q⌋₊ := rfl

@[simp, norm_cast]
theorem ceil_coe (q : ℚ≥0) : ⌈(q : ℚ)⌉₊ = ⌈q⌉₊ := rfl

@[simp, norm_cast]
theorem coe_floor (q : ℚ≥0) : ↑⌊q⌋₊ = ⌊(q : ℚ)⌋ := Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]
theorem coe_ceil (q : ℚ≥0) : ↑⌈q⌉₊ = ⌈(q : ℚ)⌉ := Int.natCast_ceil_eq_ceil q.coe_nonneg

protected theorem floor_def (q : ℚ≥0) : ⌊q⌋₊ = q.num / q.den := by
  rw [← Int.natCast_inj, NNRat.coe_floor, Rat.floor_def', Int.natCast_ediv, den_coe, num_coe]

section Semifield

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

@[simp, norm_cast]
theorem floor_cast (x : ℚ≥0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ :=
  (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]
theorem ceil_cast (x : ℚ≥0) : ⌈(x : K)⌉₊ = ⌈x⌉₊ := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

end Semifield

section Field

variable {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[simp, norm_cast]
theorem intFloor_cast (x : ℚ≥0) : ⌊(x : K)⌋ = ⌊(x : ℚ)⌋ := by
  rw [Int.floor_eq_iff, ← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one, ← Nat.floor_eq_iff (zero_le _)]

@[simp, norm_cast]
theorem intCeil_cast (x : ℚ≥0) : ⌈(x : K)⌉ = ⌈(x : ℚ)⌉ := by
  rw [Int.ceil_eq_iff, ← coe_ceil, sub_lt_iff_lt_add]
  constructor
  · have := NNRat.cast_strictMono (K := K) <| Nat.ceil_lt_add_one <| zero_le x
    rw [NNRat.cast_add, NNRat.cast_one] at this
    refine Eq.trans_lt ?_ this
    norm_cast
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

end Field

@[norm_cast]
theorem floor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ≥0)⌋₊ = n / d :=
  Rat.natFloor_natCast_div_natCast n d

end NNRat

namespace Mathlib.Meta.NormNum

open Qq

/-!
### `norm_num` extesion for `Nat.ceil`
-/

theorem IsNat.natCeil {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : ℕ) : IsNat r m → IsNat (⌈r⌉₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

theorem IsInt.natCeil {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
    (r : R) (m : ℕ) : IsInt r (.negOfNat m) → IsNat (⌈r⌉₊) 0 := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

theorem IsNNRat.natCeil {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsNNRat r n d) (res : ℕ)
    (hres : ⌈(n / d : ℚ≥0)⌉₊ = res) : IsNat ⌈r⌉₊ res := by
  constructor
  rw [← hres, h.to_eq rfl rfl, ← @NNRat.ceil_cast R]
  simp

theorem IsRat.natCeil {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsRat r (.negOfNat n) d) : IsNat ⌈r⌉₊ 0 := by
  constructor
  simp [h.neg_to_eq, div_nonneg]

open Lean in
/-- `norm_num` extension for `Nat.ceil` -/
@[norm_num ⌈_⌉₊]
def evalNatCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α $instR $instLO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(IsNat.natCeil $x _ $pb)
    | .isNegNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsInt.natCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let instSemifield ← synthInstanceQ q(Semifield $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      let instFloorSemiring ← synthInstanceQ q(FloorSemiring $α)
      assertInstancesCommute
      have z : Q(ℕ) := mkRawNatLit (⌈q⌉₊)
      letI : $z =Q ⌈($n / $d : NNRat)⌉₊ := ⟨⟩
      return .isNat q(inferInstance) z q(IsNNRat.natCeil _ $n $d $h $z rfl)
    | .isNegNNRat _ q n d h => do
      let instField ← synthInstanceQ q(Field $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsRat.natCeil _ _ _ $h)
  | _, _, _ => failure

end Mathlib.Meta.NormNum
