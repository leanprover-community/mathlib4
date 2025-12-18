/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public meta import Mathlib.Tactic.NormNum.GCD

/-!
# `norm_num` extension for `IsSquare`

The extension in this file handles natural, integer, and rational numbers.

## TODO
Add extensions for `ℚ≥0`, `ℝ`, `ℝ≥0`, `ℝ≥0∞`, `ℂ` (or any algebraically closed field?), `ZMod n`.
Probably, these extensions should go to different files.
-/

public meta section

namespace Mathlib.Meta.NormNum
open Qq

theorem isSquare_nat_of_isNat (a n : ℕ) (h : IsNat a n) (m : ℕ) (hm : m * m = n) :
    IsSquare a :=
  ⟨m, h.1.trans hm.symm⟩

/-- If `m ^ 2 < n < (m + 1) ^ 2`, then `n` is not a square.
We write this condition as `k < n ≤ k + 2 * m`, where `k = m * m`. -/
theorem not_isSquare_nat_of_isNat (a n : ℕ) (h : IsNat a n) (m k : ℕ) (hm : m * m = k)
    (hk₁ : Nat.blt k n) (hk₂ : Nat.ble n (k + 2 * m)) :
    ¬IsSquare a := by
  rcases h with ⟨rfl⟩
  subst k
  rintro ⟨b, rfl⟩
  simp only [Nat.blt_eq, Nat.ble_eq, ← sq, Nat.pow_lt_pow_iff_left two_ne_zero] at hk₁ hk₂
  rw [← Nat.add_one_le_iff, ← Nat.pow_le_pow_iff_left two_ne_zero] at hk₁
  grind

theorem iff_isSquare_int_of_isNat (a : ℤ) (n : ℕ) (h : IsNat a n) : IsSquare n ↔ IsSquare a := by
  simp [h.1, Int.isSquare_natCast_iff]

theorem iff_isSquare_of_isInt_int (a : ℤ) (n : ℕ) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' ↦ by simp [h.1, h'], fun ⟨b, hb⟩ ↦ ?_⟩
  rw [h.1, Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

theorem iff_isSquare_of_isNat_rat (a : ℚ) (n : ℕ) (h : IsNat a n) :
    IsSquare n ↔ IsSquare a := by
  simp [h.1]

theorem iff_isSquare_of_isInt_rat (a : ℚ) (n : ℕ) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' ↦ by simp [h.1, h'], fun ⟨b, hb⟩ ↦ ?_⟩
  rw [h.1, Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)

theorem isSquare_of_isNNRat_rat (a : ℚ) (n d : ℕ) (hn : IsSquare n) (hd : IsSquare d)
    (ha : IsNNRat a n d) : IsSquare a := by
  rcases hn with ⟨n, rfl⟩
  rcases hd with ⟨d, rfl⟩
  use n / d
  simp [ha.to_eq, div_mul_div_comm]

theorem not_isSquare_of_isNNRat_rat_of_num (a : ℚ) (n d : ℕ) (hn : ¬IsSquare n)
    (hnd : n.Coprime d) (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl, Rat.isSquare_iff, ← Int.cast_natCast n, ← Int.cast_natCast d,
    Rat.num_div_eq_of_coprime]
  · simp [hn]
  · contrapose! hnd
    have : n ≠ 1 := by rintro rfl; simp at hn
    simp_all
  · simpa

theorem not_isSquare_of_isNNRat_rat_of_den (a : ℚ) (n d : ℕ) (hd : ¬IsSquare d) (hnd : n.Coprime d)
    (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl, Rat.isSquare_iff, ← Int.cast_natCast n, ← Int.cast_natCast d,
    ← Int.isSquare_natCast_iff (n := Rat.den _), Rat.den_div_eq_of_coprime]
  · simp [hd]
  · contrapose! hnd
    simp_all
  · simpa

theorem not_isSquare_of_isRat_neg (a : ℚ) (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0)
    (ha : IsRat a (Int.negOfNat n) d) : ¬IsSquare a := by
  rw [ha.neg_to_eq rfl rfl]
  rintro ⟨q, hq⟩
  refine absurd hq (ne_of_lt ?_)
  calc
    -(n / d : ℚ) < 0 := by rw [Left.neg_neg_iff]; apply div_pos <;> simpa [Nat.pos_iff_ne_zero]
    _ ≤ q * q := mul_self_nonneg _

open Lean

/-- `norm_num` extension for `IsSquare` on `ℕ`. -/
@[norm_num @IsSquare ℕ _ _]
def evalIsSquareNat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℕ $mulN $a) => do
    let ⟨n, pa⟩ ← deriveNat (u := 0) (α := q(ℕ)) a q(inferInstance)
    let m := Nat.sqrt n.natLit!
    if m * m = n.natLit! then
      have em : Q(ℕ) := mkRawNatLit m
      have hm : Q($em * $em = $n) := (q(Eq.refl $n) : Expr)
      assertInstancesCommute
      return .isTrue (x := q(IsSquare $a)) q(isSquare_nat_of_isNat $a $n $pa $em $hm)
    else
      have em : Q(ℕ) := mkRawNatLit m
      have ek : Q(ℕ) := mkRawNatLit (m * m)
      have hm : Q($em * $em = $ek) := (q(Eq.refl $ek) : Expr)
      have hk₁ : Q(Nat.blt $ek $n) := (q(Eq.refl true) : Expr)
      have hk₂ : Q(Nat.ble $n ($ek + 2 * $em)) := (q(Eq.refl true) : Expr)
      assertInstancesCommute
      return .isFalse q(not_isSquare_nat_of_isNat $a $n $pa $em $ek $hm $hk₁ $hk₂)
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℤ`. -/
@[norm_num @IsSquare ℤ _ _]
def evalIsSquareInt : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℤ $mulZ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_int_of_isNat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_int $a $n $pa)
      return .ofBoolResult pb
    | _ => failure
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℚ`. -/
@[norm_num @IsSquare ℚ _ _]
def evalIsSquareRat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℚ $mulQ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_of_isNat_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNNRat sQ q n d pa => do
      -- We make sure to avoid proving `Nat.Coprime $n $d` unless we need to.
      -- Also, we do not derive `IsSquare $d` unless `$n` is a square
      match ← deriveBool q(IsSquare $n) with
      | .mk true pn =>
        match ← deriveBool q(IsSquare $d) with
        | .mk true pd =>
          assertInstancesCommute
          return .isTrue q(isSquare_of_isNNRat_rat $a $n $d $pn $pd $pa)
        | .mk false pd =>
          let ⟨e, he⟩ := Tactic.NormNum.proveNatGCD n d
          have : $e =Q 1 := ⟨⟩
          assertInstancesCommute
          return .isFalse q(not_isSquare_of_isNNRat_rat_of_den $a $n $d $pd $he $pa)
      | .mk false pn =>
        let ⟨e, he⟩ := Tactic.NormNum.proveNatGCD n d
        have : $e =Q 1 := ⟨⟩
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isNNRat_rat_of_num $a $n $d $pn $he $pa)
    | .isNegNNRat sQ q n d pa => do
      match ← deriveBool q($n = 0), ← deriveBool q($d = 0) with
      | .mk false pn, .mk false pd =>
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isRat_neg $a $n $d $pn $pd $pa)
      | _, _ => failure
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum
