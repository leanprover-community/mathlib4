/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Core
import Mathlib.Util.Simp

namespace Mathlib
open Lean Meta

initialize registerTraceClass `Tactic.norm_num

/--
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def _root_.Lean.Expr.numeral? (e : Expr) : Option Nat :=
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
  | _, _, _, _, _, rfl, rfl, rfl => Nat.cast_add.symm

theorem isNat_mul {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
    isNat a a' → isNat b b' → Nat.mul a' b' = c → isNat (a * b) c
  | _, _, _, _, _, rfl, rfl, rfl => Nat.cast_mul.symm

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

theorem eval_eq_of_isNat {α} [Semiring α] :
  (a b : α) → (n : ℕ) → isNat a n → isNat b n → a = b
  | _, _, _, rfl, rfl => rfl

/--
Constructs a proof that the original expression is true
given a simp result which simplifies the target to `True`.
-/
def _root_.Lean.Meta.Simp.Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

/-- A simp plugin which calls `NormNum.eval`. -/
def tryNormNum? (e : Expr) : SimpM (Option Simp.Step) :=
  try return some (Simp.Step.done (← eval e)) catch _ => return none

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← derive e).ofTrue

  /-- The `Methods` to use when `useSimp` is enabled. -/
  @[inline] partial def methodsSimp : Simp.Methods where
    pre := (Simp.preDefault · discharge)
    post e := do Simp.andThen (← Simp.postDefault e discharge) tryNormNum?
    discharge? := discharge

  /-- The `Methods` to use when `useSimp` is disabled. -/
  @[inline] partial def methodsNoSimp : Simp.Methods where
    post e := Simp.andThen (.visit { expr := e }) tryNormNum?
    discharge? := discharge

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def derive (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := if useSimp then methodsSimp else methodsNoSimp)
end

-- FIXME: had to inline a bunch of stuff from `simpGoal` here
/--
The core of `norm_num` as a tactic in `MetaM`.

* `g`: The goal to simplify
* `ctx`: The simp context, constructed by `mkSimpContext` and
  containing any additional simp rules we want to use
* `fvarIdsToSimp`: The selected set of hypotheses used in the location argument
* `simplifyTarget`: true if the target is selected in the location argument
* `useSimp`: true if we used `norm_num` instead of `norm_num1`
-/
def normNumAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
    let r ← derive ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← derive ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Elab.Tactic in
/--
Elaborates a call to `norm_num only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
-- FIXME: had to inline a bunch of stuff from `mkSimpContext` and `simpLocation` here
def elabNormNum (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let simpTheorems ←
    if !useSimp || simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  if starArg then
    let mut simpTheorems := ctx.simpTheorems
    for h in ← getPropHyps do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    ctx := { ctx with simpTheorems }
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => normNumAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => normNumAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]

end NormNum
end Meta

namespace Tactic

open Lean.Parser.Tactic Meta.NormNum

/-- Normalize numerical expressions. -/
elab "norm_num" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)

end Tactic
end Mathlib
