/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

/-! # `norm_num` extensions for GCD-adjacent functions

This module defines some `norm_num` extensions for functions such as
`Nat.gcd`, `Nat.lcm`, `Int.gcd`, and `Int.lcm`.

Note that `Nat.coprime` is reducible and defined in terms of `Nat.gcd`, so the `Nat.gcd` extension
also indirectly provides a `Nat.coprime` extension.
-/

namespace Tactic

namespace NormNum

theorem int_gcd_helper' {d : ℕ} {x y : ℤ} (a b : ℤ) (h₁ : (d : ℤ) ∣ x) (h₂ : (d : ℤ) ∣ y)
    (h₃ : x * a + y * b = d) : Int.gcd x y = d := by
  refine Nat.dvd_antisymm ?_ (Int.natCast_dvd_natCast.1 (Int.dvd_gcd h₁ h₂))
  rw [← Int.natCast_dvd_natCast, ← h₃]
  apply dvd_add
  · exact Int.gcd_dvd_left.mul_right _
  · exact Int.gcd_dvd_right.mul_right _

theorem nat_gcd_helper_dvd_left (x y : ℕ) (h : y % x = 0) : Nat.gcd x y = x :=
  Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)

theorem nat_gcd_helper_dvd_right (x y : ℕ) (h : x % y = 0) : Nat.gcd x y = y :=
  Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)

theorem nat_gcd_helper_2 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : x * a = y * b + d) : Nat.gcd x y = d := by
  rw [← Int.gcd_natCast_natCast]
  apply int_gcd_helper' a (-b)
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hu))
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hv))
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add']
  exact mod_cast h

theorem nat_gcd_helper_1 (d x y a b : ℕ) (hu : x % d = 0) (hv : y % d = 0)
    (h : y * b = x * a + d) : Nat.gcd x y = d :=
  (Nat.gcd_comm _ _).trans <| nat_gcd_helper_2 _ _ _ _ _ hv hu h

theorem nat_gcd_helper_1' (x y a b : ℕ) (h : y * b = x * a + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_1 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

theorem nat_gcd_helper_2' (x y a b : ℕ) (h : x * a = y * b + 1) :
    Nat.gcd x y = 1 :=
  nat_gcd_helper_2 1 _ _ _ _ (Nat.mod_one _) (Nat.mod_one _) h

theorem nat_lcm_helper (x y d m : ℕ) (hd : Nat.gcd x y = d)
    (d0 : Nat.beq d 0 = false)
    (dm : x * y = d * m) : Nat.lcm x y = m :=
  mul_right_injective₀ (Nat.ne_of_beq_eq_false d0) <| by
    dsimp only -- Porting note: the `dsimp only` was not necessary in Lean3.
    rw [← dm, ← hd, Nat.gcd_mul_lcm]

theorem int_gcd_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.gcd x' y' = d) :
    Int.gcd x y = d := by subst_vars; rw [Int.gcd_def]

theorem int_lcm_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.lcm x' y' = d) :
    Int.lcm x y = d := by subst_vars; rw [Int.lcm_def]

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

theorem isNat_gcd : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.gcd nx ny = z → IsNat (Nat.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isNat_lcm : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.lcm nx ny = z → IsNat (Nat.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

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
      have pq : Q(Nat.mod $ey $ex = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ex, q(nat_gcd_helper_dvd_left $ex $ey $pq)⟩
    else if d = y then
      have pq : Q(Nat.mod $ex $ey = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
      ⟨ey, q(nat_gcd_helper_dvd_right $ex $ey $pq)⟩
    else
      have ea' : Q(ℕ) := mkRawNatLit a.natAbs
      have eb' : Q(ℕ) := mkRawNatLit b.natAbs
      if d = 1 then
        if a ≥ 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + 1) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨mkRawNatLit 1, q(nat_gcd_helper_2' $ex $ey $ea' $eb' $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + 1) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨mkRawNatLit 1, q(nat_gcd_helper_1' $ex $ey $ea' $eb' $pt)⟩
      else
        have ed : Q(ℕ) := mkRawNatLit d
        have pu : Q(Nat.mod $ex $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        have pv : Q(Nat.mod $ey $ed = 0) := (q(Eq.refl (nat_lit 0)) : Expr)
        if a ≥ 0 then
          have pt : Q($ex * $ea' = $ey * $eb' + $ed) := (q(Eq.refl ($ex * $ea')) : Expr)
          ⟨ed, q(nat_gcd_helper_2 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩
        else
          have pt : Q($ey * $eb' = $ex * $ea' + $ed) := (q(Eq.refl ($ey * $eb')) : Expr)
          ⟨ed, q(nat_gcd_helper_1 $ed $ex $ey $ea' $eb' $pu $pv $pt)⟩

@[norm_num Nat.gcd _ _]
def evalNatGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.gcd $x $y := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatGCD ex ey
  return .isNat sℕ ed q(isNat_gcd $p $q $pf)

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
    have pm : Q($ex * $ey = $ed * $em) := (q(Eq.refl ($ex * $ey)) : Expr)
    ⟨em, q(nat_lcm_helper $ex $ey $ed $em $pd $p0 $pm)⟩

/-- Evaluates the `Nat.lcm` function. -/
@[norm_num Nat.lcm _ _]
def evalNatLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Nat.lcm $x $y := ⟨⟩
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨ex, p⟩ ← deriveNat x sℕ
  let ⟨ey, q⟩ ← deriveNat y sℕ
  let ⟨ed, pf⟩ := proveNatLCM ex ey
  return .isNat sℕ ed q(isNat_lcm $p $q $pf)

/-- Given two integers, return their GCD and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
def proveIntGCD (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.gcd $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatGCD ex' ey'
  ⟨ed, q(int_gcd_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.gcd` function. -/
@[norm_num Int.gcd _ _]
def evalIntGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.gcd $x $y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntGCD ex ey
  return .isNat _ ed q(isInt_gcd $p $q $pf)

/-- Given two integers, return their LCM and an equality proof.
Panics if `ex` or `ey` aren't integer literals. -/
def proveIntLCM (ex ey : Q(ℤ)) : (ed : Q(ℕ)) × Q(Int.lcm $ex $ey = $ed) :=
  let ⟨ex', hx⟩ := rawIntLitNatAbs ex
  let ⟨ey', hy⟩ := rawIntLitNatAbs ey
  let ⟨ed, pf⟩ := proveNatLCM ex' ey'
  ⟨ed, q(int_lcm_helper $hx $hy $pf)⟩

/-- Evaluates the `Int.lcm` function. -/
@[norm_num Int.lcm _ _]
def evalIntLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let ⟨ex, p⟩ ← deriveInt x _
  let ⟨ey, q⟩ ← deriveInt y _
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℕ := ⟨⟩
  haveI' : $e =Q Int.lcm $x $y := ⟨⟩
  let ⟨ed, pf⟩ := proveIntLCM ex ey
  return .isNat _ ed q(isInt_lcm $p $q $pf)

end NormNum

end Tactic
