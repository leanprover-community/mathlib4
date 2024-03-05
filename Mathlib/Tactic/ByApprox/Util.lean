import Mathlib.Lean.Expr
import Mathlib.Util.Qq
import Mathlib.Tactic.NormNum.Core

import Mathlib.Tactic.ByApprox.Lemmas

import Std.Data.Rat.Basic


namespace Mathlib.Tactic.ByApprox

open Lean hiding Rat
open Qq Meta

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType)

private def mkAppMFinal (solver : MVarId → MetaM Unit) (f : Expr) (args : Array Expr)
    (instMVars : Array MVarId) (solverMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  solverMVars.forM fun mvarId => do
    if !(← mvarId.isAssigned) then
      solver mvarId

  let result ← instantiateMVars (mkAppN f args)
  if (← hasAssignableMVar result) then
    throwError ("result contains metavariables" ++ indentExpr result)
  return result

private partial def mkAppAutoMAux (solver : MVarId → MetaM Unit) (f : Expr)
    (xs : Array (Option Expr)) : Nat → Array Expr → Nat → Array MVarId → Array MVarId → Expr →
    MetaM Expr
  | i, args, j, instMVars, solverMVars, Expr.forallE n d b bi => do
    let d  := d.instantiateRevRange j args.size args
    if h : i < xs.size then
      match xs.get ⟨i, h⟩ with
      | none =>
        match bi with
        | BinderInfo.instImplicit => do
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          mkAppAutoMAux solver f xs (i+1) (args.push mvar) j (instMVars.push mvar.mvarId!)
            solverMVars b
        | _                       => do
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          mkAppAutoMAux solver f xs (i+1) (args.push mvar) j instMVars
            (solverMVars.push mvar.mvarId!) b
      | some x =>
        let xType ← inferType x
        if (← isDefEq d xType) then
          mkAppAutoMAux solver f xs (i+1) (args.push x) j instMVars solverMVars b
        else
          throwAppTypeMismatch (mkAppN f args) x
    else
      mkAppMFinal solver f args instMVars solverMVars
  | i, args, j, instMVars, solverMVars, type => do
    let type := type.instantiateRevRange j args.size args
    let type ← whnfD type
    if type.isForall then
      mkAppAutoMAux solver f xs i args args.size instMVars solverMVars type
    else if i == xs.size then
      mkAppMFinal solver f args instMVars solverMVars
    else do
      let xs : Array Expr := xs.foldl (fun r x? => match x? with | none => r | some x => r.push x) #[]
      throwError ("too many arguments provided to" ++ indentExpr f ++ Format.line ++ "arguments" ++ xs)


def mkAppAutoM (constName : Name) (solver : MVarId → MetaM Unit) (xs : Array (Option Expr)) :
    MetaM Expr := do
  withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    mkAppAutoMAux solver f xs 0 #[] 0 #[] #[] fType

partial def decideExpr (target: Q(Prop)) : MetaM Q($target) := do
  let target ← instantiateMVars target
  mkAppOptM ``of_decide_eq_true #[target, none, q(Eq.refl true)]

def mkAppNormNum (constName : Name) (xs : Array (Option Expr)) : MetaM Expr :=
  mkAppAutoM constName (fun mvar => do
    try mvar.assign (← decideExpr (← mvar.getType))
    catch _ =>
    let results ← Meta.NormNum.normNumAt mvar (← mkSimpContext) #[]
    if results.isSome then
      throwError "norm_num failed to fill goal of type {← mvar.getType}, remains to prove {← results.get!.2.getType}"
  ) xs

-- partial def decideRational (target : Q(Prop)) : MetaM Q($target) := do
--   let target ← withReducible $ whnf (← instantiateMVars target)
--   match target.getAppFnArgs with
--   | (``LE.le, #[Rat, _, a, b]) => mkAppDecideM ``le_of_int_le #[]
--   | _ => decideExpr target

-- def mkAppDecideM (constName : Name) (xs : Array (Option Expr)) : MetaM Expr :=
--   mkAppAutoM constName (fun mvar => do mvar.assign (← decideRationalExpr (← mvar.getType))) xs

partial def mkRatExpr (val : ℚ) : Q(ℚ) :=
  let n : Int := val.num
  let d : Nat := val.den
  q(Int.cast $n / @Nat.cast ℚ Semiring.toNatCast $d)

partial def mkRatLeProof (a b : ℚ) : MetaM Expr := do
  mkAppNormNum ``le_of_int_le #[q(Rat), none, toExpr a.num, toExpr b.num,
    toExpr a.den, toExpr b.den, none, none, none]
