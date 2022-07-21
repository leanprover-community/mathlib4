/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Core
import Mathlib.Util.Simp

namespace Lean

initialize registerTraceClass `Tactic.norm_num

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

/-- Given
  - `u : Level`,
  - `$α : Type $u`,
  - `$sα : Semiring $α` and
  - `$e : $α` where `e` is reducible to a number literal.
  Produces a pair `(c, p)` where
  - `n` is a natural number literal and
  - `$p : isNat $e $n`
-/
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

/-- Given
  - `$e : $α` where `e` is reducible to a number literal.
  Produces a simp-result `(n, p)` where
  - `n` is a natural number literal and
  - `$p : $e = OfNat.ofNat $n`
  Providing we have `LawfulOfNat $α $n`.
-/
def eval (e : Expr) : MetaM Simp.Result := do
  let α ← inferType e
  let .succ u ← getLevel α | throwError "fail"
  let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
  let (ln, p) ← evalIsNat u α sα e
  let ofNatInst ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α ln)
  let lawfulInst ← synthInstance (mkApp4 (mkConst ``LawfulOfNat [u]) α sα ln ofNatInst)
  let expr := mkApp3 (mkConst ``OfNat.ofNat [u]) α ln ofNatInst
  let pf := mkApp7 (mkConst ``eval_of_isNat [u]) α sα ln ofNatInst lawfulInst e p
  return {expr, proof? := pf}

open Simp in
/-- Traverses the given expression using simp and normalises any numbers it finds. -/
def derive (ctx : Simp.Context) (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e
  let nosimp := (← getOptions).getBool `norm_num.nosimp
  let methods := if nosimp then {} else Simp.DefaultMethods.methods
  let r ← Simp.main e ctx
    { methods with
      post := fun e => do try return Simp.Step.done (← eval e) catch _ => methods.post e }
  trace[Tactic.norm_num] "before: {e}\n after: {r.expr}"

  return r

theorem eval_eq_of_isNat {α} [Semiring α] :
  (a b : α) → (n : ℕ) → isNat a n → isNat b n → a = b
  | _, _, _, rfl, rfl => rfl

/-- Returns the proof that `a = b` using normnum. -/
def evalEq (α a b : Expr) : MetaM Expr := do
  let .succ u ← getLevel α | throwError "fail: expected {α} to be a type."
  let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
  let (ln, pa) ← evalIsNat u α sα a
  let (ln', pb) ← evalIsNat u α sα b
  guard (ln.natLit! == ln'.natLit!)
  pure $ mkApp7 (mkConst ``eval_eq_of_isNat [u]) α sα a b ln pa pb

open Lean Elab Tactic Conv

/-- Normnums a target. -/
def normNumTarget (ctx : Simp.Context) : TacticM Unit := do
  liftMetaTactic1 fun mvarId => do
    let tgt ← instantiateMVars (← getMVarType mvarId)
    let prf ← derive ctx tgt
    let newGoal ← applySimpResultToTarget mvarId tgt prf
    let t ← inferType (mkMVar newGoal)
    if t.isConstOf ``True then
      assignExprMVar newGoal (mkConst ``True.intro)
      return none
    return some newGoal

/-- Normnums a hypothesis. -/
def normNumHyp (ctx : Simp.Context) (fvarId: FVarId) : TacticM Unit :=
  liftMetaTactic1 fun mvarId => do
    let hyp ← instantiateMVars (← getLocalDecl fvarId).type
    let prf ← derive ctx hyp
    let (some (_newHyp, newGoal)) ← applySimpResultToLocalDecl mvarId fvarId prf false
      | throwError "Failed to apply norm_num to hyp."
    return newGoal

open Meta Elab Tactic in
/-- Elaborator helper for norm num. -/
def elabNormNum (args: Syntax) (loc : Syntax) : TacticM Unit := do
  -- [todo] are there norm_num simp lemmas?
  let simpTheorems ← ({} : SimpTheorems).addConst ``eq_self
  let congrTheorems ← Meta.getSimpCongrTheorems
  let eraseLocal := false
  let kind := SimpKind.simp
  let mut ctx : Simp.Context := {
    config      := {}
    simpTheorems := #[simpTheorems]
    congrTheorems
  }
  let r ← Lean.Elab.Tactic.elabSimpArgs args (eraseLocal := eraseLocal) (kind := kind) ctx
  ctx := r.ctx
  let loc := expandOptLocation loc
  withLocation loc
    (atLocal := Meta.NormNum.normNumHyp ctx)
    (atTarget := Meta.NormNum.normNumTarget ctx)
    (failed := fun _ => throwError "norm_num failed")

end NormNum
end Meta

namespace Tactic

open Lean.Parser.Tactic

/-- Normalize numerical expressions. -/
elab "norm_num" args:(("[" simpArg,* "]")?) loc:(location ?) : tactic =>
  withOptions (·.setBool `norm_num.nosimp false)
  <| Meta.NormNum.elabNormNum args loc

/-- Basic version of `norm_num` that does not call `simp`. -/
elab "norm_num1" loc:(location ?) : tactic =>
  withOptions (·.setBool `norm_num.nosimp true)
  <| Meta.NormNum.elabNormNum (Syntax.missing) loc

end Tactic

end Lean
