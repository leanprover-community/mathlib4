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

namespace NormNum

def isNat [Semiring α] (a : α) (n : ℕ) := a = n

class LawfulOfNat (α) [Semiring α] (n) [OfNat α n] : Prop where
  isNat_ofNat : isNat (@OfNat.ofNat _ n ‹_› : α) n

instance (α) [Semiring α] [Nat.AtLeastTwo n] : LawfulOfNat α n := ⟨rfl⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 0) := ⟨Nat.cast_zero.symm⟩
instance (α) [Semiring α] : LawfulOfNat α (nat_lit 1) := ⟨Nat.cast_one.symm⟩
instance : LawfulOfNat Nat n := ⟨show n = Nat.cast n by simp⟩
instance : LawfulOfNat Int n := ⟨show Int.ofNat n = Nat.cast n by simp⟩

theorem isNat_rawNat (n : ℕ) : isNat n n := LawfulOfNat.isNat_ofNat

class LawfulZero (α) [Semiring α] [Zero α] : Prop where
  isNat_zero : isNat (Zero.zero : α) (nat_lit 0)

instance (α) [Semiring α] : LawfulZero α := ⟨Nat.cast_zero.symm⟩

class LawfulOne (α) [Semiring α] [One α] : Prop where
  isNat_one : isNat (One.one : α) (nat_lit 1)

instance (α) [Semiring α] : LawfulOne α := ⟨Nat.cast_one.symm⟩

theorem isNat_add {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  isNat a a' → isNat b b' → Nat.add a' b' = c → isNat (a + b) c
| _, _, _a', _b', _, rfl, rfl, rfl => Nat.cast_add.symm

theorem isNat_mul {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  isNat a a' → isNat b b' → Nat.mul a' b' = c → isNat (a * b) c
| _, _, _a', _b', _, rfl, rfl, rfl => Nat.cast_mul.symm

theorem isNat_pow {α} [Semiring α] : (a : α) → (b a' b' c : Nat) →
  isNat a a' → isNat b b' → Nat.pow a' b' = c → isNat (a ^ b) c
| _, _, _, _, _, rfl, rfl, rfl => by simp [isNat]

def instSemiringNat : Semiring Nat := inferInstance

theorem isNat_cast {R} [Semiring R] (n m : Nat) :
    isNat n m → isNat (n : R) m := by
  rintro ⟨⟩; rfl

partial def evalIsNat (u : Level) (α sα e : Expr) : MetaM (Expr × Expr) := do
  let (n, p) ← match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => evalBinOp ``NormNum.isNat_add (·+·) a b
  | (``HMul.hMul, #[_, _, _, _, a, b]) => evalBinOp ``NormNum.isNat_mul (·*·) a b
  | (``HPow.hPow, #[_, _, _, _, a, b]) => evalPow ``NormNum.isNat_pow (·^·) a b
  | (``OfNat.ofNat, #[_, ln, inst]) =>
    unless ln.isNatLit do throwError "fail"
    let lawful ← synthInstance (mkApp4 (mkConst ``LawfulOfNat [u]) α sα ln inst)
    pure (ln, mkApp5 (mkConst ``LawfulOfNat.isNat_ofNat [u]) α sα ln inst lawful)
  | (``Zero.zero, #[_, inst]) =>
    let lawful ← synthInstance (mkApp3 (mkConst ``LawfulZero [u]) α sα inst)
    pure (mkNatLit 0, mkApp4 (mkConst ``LawfulZero.isNat_zero [u]) α sα inst lawful)
  | (``One.one, #[_, inst]) =>
    let lawful ← synthInstance (mkApp3 (mkConst ``LawfulOne [u]) α sα inst)
    pure (mkNatLit 1, mkApp4 (mkConst ``LawfulOne.isNat_one [u]) α sα inst lawful)
  | (``Nat.cast, #[_, _, n])  =>
    let (m, pm) ← evalIsNat levelZero (mkConst ``Nat) (mkConst ``instSemiringNat) n
    pure (m, mkApp5 (mkConst ``isNat_cast [u]) α sα n m pm)
  | _ =>
    unless e.isNatLit do throwError "fail {e}"
    pure (e, mkApp (mkConst ``isNat_rawNat) e)
  pure (n, mkApp2 (mkConst ``id [levelZero]) (mkApp4 (mkConst ``isNat [u]) α sα e n) p)
where
  evalBinOp (name : Name) (f : Nat → Nat → Nat) (a b : Expr) : MetaM (Expr × Expr) := do
    let (la, pa) ← evalIsNat u α sα a
    let (lb, pb) ← evalIsNat u α sα b
    let a' := la.natLit!
    let b' := lb.natLit!
    let c' := f a' b'
    let lc := mkRawNatLit c'
    pure (lc, mkApp10 (mkConst name [u]) α sα a b la lb lc pa pb (← mkEqRefl lc))
  evalPow (name : Name) (f : Nat → Nat → Nat) (a b : Expr) : MetaM (Expr × Expr) := do
    let (la, pa) ← evalIsNat u α sα a
    let (lb, pb) ← evalIsNat levelZero (mkConst ``Nat) (mkConst ``instSemiringNat) b
    let a' := la.natLit!
    let b' := lb.natLit!
    let c' := f a' b'
    let lc := mkRawNatLit c'
    pure (lc, mkApp10 (mkConst name [u]) α sα a b la lb lc pa pb (← mkEqRefl lc))

theorem eval_of_isNat {α} [Semiring α] (n) [OfNat α n] [LawfulOfNat α n] :
  (a : α) → isNat a n → a = OfNat.ofNat n
| _, rfl => LawfulOfNat.isNat_ofNat.symm

def eval (e : Expr) : MetaM (Expr × Expr) := do
  let α ← inferType e
  let .succ u ← getLevel α | throwError "fail"
  let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
  let (ln, p) ← evalIsNat u α sα e
  let ofNatInst ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α ln)
  let lawfulInst ← synthInstance (mkApp4 (mkConst ``LawfulOfNat [u]) α sα ln ofNatInst)
  pure (mkApp3 (mkConst ``OfNat.ofNat [u]) α ln ofNatInst,
    mkApp7 (mkConst ``eval_of_isNat [u]) α sα ln ofNatInst lawfulInst e p)

theorem eval_eq_of_isNat {α} [Semiring α] :
  (a b : α) → (n : ℕ) → isNat a n → isNat b n → a = b
| _, _, _, rfl, rfl => rfl

def evalEq (α a b : Expr) : MetaM Expr := do
  let .succ u ← getLevel α | throwError "fail"
  let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
  let (ln, pa) ← evalIsNat u α sα a
  let (ln', pb) ← evalIsNat u α sα b
  guard (ln.natLit! == ln'.natLit!)
  pure $ mkApp7 (mkConst ``eval_eq_of_isNat [u]) α sα a b ln pa pb

end NormNum
end Meta

namespace Tactic

open Lean.Parser.Tactic in
syntax (name := normNum) "norm_num" (" [" simpArg,* "]")? (ppSpace location)? : tactic

open Meta Elab.Tactic in
elab_rules : tactic | `(tactic| norm_num) => do
  liftMetaTactic fun g => do
    let some (α, lhs, rhs) ← matchEq? (← getMVarType g) | throwError "fail"
    let p ← NormNum.evalEq α lhs rhs
    assignExprMVar g p
    pure []

end Tactic

end Lean

variable (α) [Semiring α]
example : (1 + 0 : α) = (0 + 1 : α) := by norm_num
example : (0 + (2 + 3) + 1 : α) = 6 := by norm_num
example : (70 * (33 + 2) : α) = 2450 := by norm_num
example : (8 + 2 ^ 2 * 3 : α) = 20 := by norm_num
example : ((2 * 1 + 1) ^ 2 : α) = (3 * 3 : α) := by norm_num
