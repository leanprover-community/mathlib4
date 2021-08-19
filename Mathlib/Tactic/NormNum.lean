/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Core

namespace Lean

/--
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def Expr.numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

namespace Meta

def mkOfNatLit (u : Level) (α sα n : Expr) : Expr :=
  let inst := mkApp3 (mkConst ``Numeric.OfNat [u]) α n sα
  mkApp3 (mkConst ``OfNat.ofNat [u]) α n inst

namespace NormNum

theorem ofNat_nat (n : ℕ) : n = @OfNat.ofNat _ n (@Numeric.OfNat _ _ _) := rfl
set_option pp.all true

theorem ofNat_add {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' + b' = c → a + b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_add _ _).symm

theorem ofNat_mul {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' * b' = c → a * b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_mul _ _).symm

theorem ofNat_pow {α} [Semiring α] : (a : α) → (n a' c : Nat) →
  a = OfNat.ofNat a' → a'^n = c → a ^ n = OfNat.ofNat c
| _, _, _, _, rfl, rfl => (Semiring.ofNat_pow _ _).symm

partial def eval' (e : Expr) : MetaM (Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, α, _, a, b]) => evalBinOp ``NormNum.ofNat_add (·+·) α a b
  | (``HMul.hMul, #[_, _, α, _, a, b]) => evalBinOp ``NormNum.ofNat_mul (·*·) α a b
  | (``HPow.hPow, #[_, _, α, _, a, n]) => evalPow ``NormNum.ofNat_pow (·^·) α a n
  | (``OfNat.ofNat, #[α, ln, _]) =>
    match ← ln.natLit? with
    | some 0 =>
      let Level.succ u _ ← getLevel α | throwError "fail"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let e ← mkOfNatLit u α nα (mkRawNatLit 0)
      let p ← mkEqSymm (mkApp2 (mkConst ``Semiring.ofNat_zero [u]) α sα)
      (e, p)
    | some 1 =>
      let Level.succ u _ ← getLevel α | throwError "fail"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let e ← mkOfNatLit u α nα (mkRawNatLit 1)
      let p ← mkEqSymm (mkApp2 (mkConst ``Semiring.ofNat_one [u]) α sα)
      (e, p)
    | some _ => pure (e, ← mkEqRefl e)
    | none => throwError "fail"
  | _ =>
    if e.isNatLit then
      (mkOfNatLit levelZero (mkConst ``Nat) (mkConst ``Nat.instNumericNat) e,
       mkApp (mkConst ``ofNat_nat) e)
    else throwError "fail"
where
  evalBinOp (name : Name) (f : Nat → Nat → Nat) (α a b : Expr) : MetaM (Expr × Expr) := do
    let Level.succ u _ ← getLevel α | throwError "fail"
    let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
    let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
    let (a', pa) ← eval' a
    let (b', pb) ← eval' b
    let la := Expr.getRevArg! a' 1
    let lb := Expr.getRevArg! b' 1
    let lc := mkRawNatLit (f la.natLit! lb.natLit!)
    let c := mkOfNatLit u α nα lc
    (c, mkApp10 (mkConst name [u]) α sα a b la lb lc pa pb (← mkEqRefl lc))
  evalPow (name : Name) (f : Nat → Nat → Nat) (α a n : Expr) : MetaM (Expr × Expr) := do
    let Level.succ u _ ← getLevel α | throwError "fail"
    let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
    let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
    let (a', pa) ← eval' a
    let la := Expr.getRevArg! a' 1
    let some nn ← n.numeral? | throwError "fail"
    let lc := mkRawNatLit (f la.natLit! nn)
    let c := mkOfNatLit u α nα lc
    (c, mkApp8 (mkConst name [u]) α sα a n la lc pa (← mkEqRefl lc))

def eval (e : Expr) : MetaM (Expr × Expr) := do
  let (e', p) ← eval' e
  e'.withApp fun f args => do
    if f.isConstOf ``OfNat.ofNat then
      let #[α,ln,_] ← args | throwError "fail"
      let some n ← ln.natLit? | throwError "fail"
      if n = 0 then
        let Level.succ u _ ← getLevel α | throwError "fail"
        let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
        let nα ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α (mkRawNatLit 0))
        let e'' ←  mkApp3 (mkConst ``OfNat.ofNat [u]) α (mkRawNatLit 0) nα
        let p' ← mkEqTrans p (mkApp2 (mkConst ``Semiring.ofNat_zero [u]) α sα)
        (e'', p')
      else if n = 1 then
        let Level.succ u _ ← getLevel α | throwError "fail"
        let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
        let nα ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α (mkRawNatLit 1))
        let e'' ←  mkApp3 (mkConst ``OfNat.ofNat [u]) α (mkRawNatLit 1) nα
        let p' ← mkEqTrans p (mkApp2 (mkConst ``Semiring.ofNat_one [u]) α sα)
        (e'', p')
      else (e', p)
    else (e', p)

end NormNum
end Meta

syntax (name := Parser.Tactic.normNum) "normNum" : tactic

open Meta Elab Tactic

@[tactic normNum] def Tactic.evalNormNum : Tactic := fun stx =>
  liftMetaTactic fun g => do
    let some (α, lhs, rhs) ← matchEq? (← getMVarType g) | throwError "fail"
    let (lhs₂, lp) ← NormNum.eval' lhs
    let (rhs₂, rp) ← NormNum.eval' rhs
    unless ← isDefEq lhs₂ rhs₂ do throwError "fail"
    let p ← mkEqTrans lp (← mkEqSymm rp)
    assignExprMVar g p
    pure []

end Lean

variable (α) [Semiring α]
example : (1 + 0 : α) = (0 + 1 : α) := by normNum
example : (0 + (2 + 3) + 1 : α) = 6 := by normNum
example : (70 * (33 + 2) : α) = 2450 := by normNum
example : (8 + 2 ^ 2 * 3 : α) = 20 := by normNum
example : ((2 * 1 + 1) ^ 2 : α) = (3 * 3 : α) := by normNum
