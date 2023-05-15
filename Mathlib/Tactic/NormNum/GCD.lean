/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for GCD-adjacent functions

This module defines some `norm_num` extensions for functions such as
`Nat.gcd`, `Nat.lcm`, `Nat.coprime`, `Int.gcd`, and `Int.lcm`.
-/

namespace Tactic

namespace NormNum

theorem int_gcd_helper' {d : ℕ} {x y : ℤ} (a b : ℤ) (h₁ : (d : ℤ) ∣ x) (h₂ : (d : ℤ) ∣ y)
    (h₃ : x * a + y * b = d) : Int.gcd x y = d := by
  refine' Nat.dvd_antisymm _ (Int.coe_nat_dvd.1 (Int.dvd_gcd h₁ h₂))
  rw [← Int.coe_nat_dvd, ← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left _ _).mul_right _
  · exact (Int.gcd_dvd_right _ _).mul_right _
#align tactic.norm_num.int_gcd_helper' Tactic.NormNum.int_gcd_helper'

theorem nat_gcd_helper_dvd_left (x y : ℕ) (h : y % x = 0) : Nat.gcd x y = x :=
  Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)
#align tactic.norm_num.nat_gcd_helper_dvd_left Tactic.NormNum.nat_gcd_helper_dvd_left

theorem nat_gcd_helper_dvd_right (x y : ℕ) (h : x % y = 0) : Nat.gcd x y = y :=
  Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
#align tactic.norm_num.nat_gcd_helper_dvd_right Tactic.NormNum.nat_gcd_helper_dvd_right

theorem nat_gcd_helper_2 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : Nat.beq (x * a) (y * b + d) = true) : Nat.gcd x y = d := by
  rw [← Int.coe_nat_gcd];
  apply int_gcd_helper' a (-b)
    (Int.coe_nat_dvd.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.coe_nat_dvd.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add']
  norm_cast
  exact Nat.eq_of_beq_eq_true h
#align tactic.norm_num.nat_gcd_helper_2 Tactic.NormNum.nat_gcd_helper_2

theorem nat_gcd_helper_1 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : Nat.beq (y * b) (x * a + d) = true) : Nat.gcd x y = d :=
  (Nat.gcd_comm _ _).trans <| nat_gcd_helper_2 _ _ _ _ _ hv hu h
#align tactic.norm_num.nat_gcd_helper_1 Tactic.NormNum.nat_gcd_helper_1

theorem nat_lcm_helper (x y d m : ℕ) (hd : Nat.gcd x y = d)
    (d0 : Nat.beq d 0 = false)
    (dm : Nat.beq (x * y) (d * m) = true) : Nat.lcm x y = m :=
  mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) <| by
    dsimp only; -- Porting note: the `dsimp only` was not necessary in Lean3.
    rw [← Nat.eq_of_beq_eq_true dm, ← hd, Nat.gcd_mul_lcm]
#align tactic.norm_num.nat_lcm_helper Tactic.NormNum.nat_lcm_helper

theorem not_coprime_helper {x y d : Nat} (h : Nat.gcd x y = d) (h' : Nat.beq d 1 = false) :
    ¬ Nat.coprime x y :=
  by cases h; exact fun h'' => Nat.ne_of_beq_eq_false h' (Nat.coprime_iff_gcd_eq_one.mp h'')

theorem int_gcd_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.gcd x' y' = d) :
    Int.gcd x y = d := by subst_vars; rw [Int.gcd_def]

theorem int_lcm_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.lcm x' y' = d) :
    Int.lcm x y = d := by subst_vars; rw [Int.lcm_def]

#noalign tactic.norm_num.nat_coprime_helper_zero_left
#noalign tactic.norm_num.nat_coprime_helper_zero_right
#noalign tactic.norm_num.nat_coprime_helper_1
#noalign tactic.norm_num.nat_coprime_helper_2
#noalign tactic.norm_num.nat_not_coprime_helper
#noalign tactic.norm_num.int_gcd_helper''
#noalign tactic.norm_num.int_gcd_helper_neg_left
#noalign tactic.norm_num.int_gcd_helper_neg_right
#noalign tactic.norm_num.int_lcm_helper
#noalign tactic.norm_num.int_lcm_helper_neg_left
#noalign tactic.norm_num.int_lcm_helper_neg_right

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

theorem isNat_gcd : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.gcd nx ny = z → IsNat (Nat.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isNat_lcm : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.lcm nx ny = z → IsNat (Nat.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isNat_coprime : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → Nat.coprime nx ny → Nat.coprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isNat_not_coprime : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → ¬ Nat.coprime nx ny → ¬ Nat.coprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isInt_gcd : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.gcd nx ny = z → IsNat (Int.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isInt_lcm : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.lcm nx ny = z → IsNat (Int.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Given natural number literals `ex` and `ey`, return their GCD as a natural number literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals. -/
def proveNatGCD (ex ey : Q(ℕ)) : (ed : Q(ℕ)) × Q(Nat.gcd $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
  | 0, _ => show (ed : Q(ℕ)) × Q(Nat.gcd 0 $ey = $ed) from ⟨ey, q(Nat.gcd_zero_left $ey)⟩
  | _, 0 => show (ed : Q(ℕ)) × Q(Nat.gcd $ex 0 = $ed) from ⟨ex, q(Nat.gcd_zero_right $ex)⟩
  | 1, _ => show (ed : Q(ℕ)) × Q(Nat.gcd 1 $ey = $ed) from ⟨mkRawNatLit 1, q(Nat.gcd_one_left $ey)⟩
  | _, 1 => show (ed : Q(ℕ)) × Q(Nat.gcd $ex 1 = $ed) from ⟨mkRawNatLit 1, q(Nat.gcd_one_right $ex)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have pq : Q(Nat.mod $ey $ex = 0) := (q(@Eq.refl Nat 0) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(@Eq.refl Nat 0) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ed : Q(ℕ) := mkRawNatLit d
      have pu : Q(Nat.mod $ex $ed = 0) := (q(@Eq.refl Nat 0) : Expr)
      have pv : Q(Nat.mod $ey $ed = 0) := (q(@Eq.refl Nat 0) : Expr)
      have ea' : Q(ℕ) := mkRawNatLit a.natAbs
      have eb' : Q(ℕ) := mkRawNatLit b.natAbs
      if a ≥ 0 then
        have pt : Q(Nat.beq ($ex * $ea') ($ey * $eb' + $ed) = true) := (q(Eq.refl true) : Expr)
        ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
      else
        have pt : Q(Nat.beq ($ey * $eb') ($ex * $ea' + $ed) = true) := (q(Eq.refl true) : Expr)
        ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
#align tactic.norm_num.prove_gcd_nat Tactic.NormNum.proveNatGCD

@[norm_num Nat.gcd _ _]
def evalNatGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  let pf' : Q(IsNat (Nat.gcd $x $y) $ed) := q(isNat_gcd $p $q $pf)
  return .isNat sℕ ed pf'

/-- Given natural number literals `ex` and `ey`, return their LCM as a natural number literal
and an equality proof. Panics if `ex` or `ey` aren't natural number literals. -/
def proveNatLCM (ex ey : Q(ℕ)) : (ed : Q(ℕ)) × Q(Nat.lcm $ex $ey = $ed) :=
  match ex.natLit!, ey.natLit! with
  | 0, _ =>
    show (ed : Q(ℕ)) × Q(Nat.lcm 0 $ey = $ed) from ⟨mkRawNatLit 0, q(Nat.lcm_zero_left $ey)⟩
  | _, 0 =>
    show (ed : Q(ℕ)) × Q(Nat.lcm $ex 0 = $ed) from ⟨mkRawNatLit 0, q(Nat.lcm_zero_right $ex)⟩
  | 1, _ => show (ed : Q(ℕ)) × Q(Nat.lcm 1 $ey = $ed) from ⟨ey, q(Nat.lcm_one_left $ey)⟩
  | _, 1 => show (ed : Q(ℕ)) × Q(Nat.lcm $ex 1 = $ed) from ⟨ex, q(Nat.lcm_one_right $ex)⟩
  | x, y =>
    let ⟨ed, pd⟩ := proveNatGCD ex ey
    have p0 : Q(Nat.beq $ed 0 = false) := (q(Eq.refl false) : Expr)
    have em : Q(ℕ) := mkRawNatLit (x * y / ed.natLit!)
    have pm : Q(Nat.beq ($ex * $ey) ($ed * $em) = true) := (q(Eq.refl true) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩
#align tactic.norm_num.prove_lcm_nat Tactic.NormNum.proveNatLCM

/-- Evaluates the `Nat.lcm` function. -/
@[norm_num Nat.lcm _ _]
def evalNatLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  let pf' : Q(IsNat (Nat.lcm $x $y) $ed) := q(isNat_lcm $p $q $pf)
  return .isNat sℕ ed pf'

/-- Evaluates `Nat.coprime` for the given natural number literals.
Panics if `ex` or `ey` aren't natural number literals. -/
def proveNatCoprime (ex ey : Q(ℕ)) : Q(Nat.coprime $ex $ey) ⊕ Q(¬ Nat.coprime $ex $ey) :=
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  match ed.natLit! with
  | 1 =>
    have pf' : Q(Nat.gcd $ex $ey = 1) := pf
    Sum.inl q(Nat.coprime_iff_gcd_eq_one.mpr $pf')
  | _ =>
    have edne : Q(Nat.beq $ed 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(not_coprime_helper $pf $edne)
#align tactic.norm_num.prove_coprime_nat Tactic.NormNum.proveNatCoprime

/-- Evaluates the `Nat.coprime` function. -/
@[norm_num Nat.coprime _ _]
def evalNatCoprime : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  match proveNatCoprime ex ey with
  | .inl pf =>
    have pf' : Q(Nat.coprime $x $y) := q(isNat_coprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ Nat.coprime $x $y) := q(isNat_not_coprime $p $q $pf)
    return .isFalse pf'

/-- Given two integers, return their GCD and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
def proveIntGCD (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.gcd $ex $ey = $ed) :=
  let ex' : Q(ℕ) := ex.intLitNatAbs!
  let ey' : Q(ℕ) := ey.intLitNatAbs!
  have hx : Q(($ex).natAbs = $ex') := (q(Eq.refl $ex') : Expr)
  have hy : Q(($ey).natAbs = $ey') := (q(Eq.refl $ey') : Expr)
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  have pf' : Q(Int.gcd $ex $ey = $ed) := q(int_gcd_helper $hx $hy $pf)
  ⟨ed, pf'⟩
#align tactic.norm_num.prove_gcd_int Tactic.NormNum.proveIntGCD

/-- Evaluates the `Int.gcd` function. -/
@[norm_num Int.gcd _ _]
def evalIntGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let sℤ : Q(Ring ℤ) := q(Int.instRingInt)
  let ⟨ex, p⟩ ← deriveInt x
  let ⟨ey, q⟩ ← deriveInt y
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  have pf : Q(Int.gcd $ex $ey = $ed) := pf
  have pf' : Q(IsNat (Int.gcd $x $y) $ed) := q(isInt_gcd $p $q $pf)
  return .isNat sℕ ed pf'

/-- Given two integers, return their LCM and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
def proveIntLCM (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.lcm $ex $ey = $ed) :=
  let ex' : Q(ℕ) := ex.intLitNatAbs!
  let ey' : Q(ℕ) := ey.intLitNatAbs!
  have hx : Q(($ex).natAbs = $ex') := (q(Eq.refl $ex') : Expr)
  have hy : Q(($ey).natAbs = $ey') := (q(Eq.refl $ey') : Expr)
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  have pf' : Q(Int.lcm $ex $ey = $ed) := q(int_lcm_helper $hx $hy $pf)
  ⟨ed, pf'⟩
#align tactic.norm_num.prove_lcm_int Tactic.NormNum.proveIntLCM

/-- Evaluates the `Int.lcm` function. -/
@[norm_num Int.lcm _ _]
def evalIntLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let sℤ : Q(Ring ℤ) := q(Int.instRingInt)
  let ⟨ex, p⟩ ← deriveInt x
  let ⟨ey, q⟩ ← deriveInt y
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  have pf : Q(Int.lcm $ex $ey = $ed) := pf
  have pf' : Q(IsNat (Int.lcm $x $y) $ed) := q(isInt_lcm $p $q $pf)
  return .isNat sℕ ed pf'

#noalign tactic.norm_num.eval_gcd

end NormNum

end Tactic
