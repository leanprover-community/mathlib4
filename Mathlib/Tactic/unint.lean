import Mathlib.Tactic.junkAttribute
import Mathlib.Tactic.RunCmd
import Std.Lean.Expr
import Mathlib.Lean.Expr.Basic

namespace Lean.Expr

open Elab Tactic Meta

/-- `getNeg e` takes an expression `e` as input.
* If `e` is of the form `¬ e'`, then it returns `(false, e')`;
* if `e` is of the form `a ≠ b`, then it returns `(false, a = b)`;
* otherwise it returns `(true, e)`.
-/
def getNeg (e : Expr) : MetaM (Bool × Expr) := do
  if e.isConst then return (true, e) else
  let we := ← whnf e
  if (we.isForall && we.bindingBody! == (.const `False [])) then
    return (false, we.bindingDomain!)
  else
    match e with
      | (.app _ unNot) => do
        if (← isDefEq e (mkNot unNot)) then pure (false, unNot) else pure (true, e)
      | _ =>
        pure (true, e)

/-- `getProps thm` takes a name `thm`, assuming that it is the name of a declaration.
It scans the environment looking for `thm`, panicking if it does not exist.
It then extracts all the hypotheses of the declaration `thm` that are of Type `Prop`.
-/
def getProps (thm : Name) : MetaM (Array Expr) := do
let env := ← getEnv
let c := env.find? thm |>.get!
--dbg_trace c.all
--dbg_trace ← ppExpr c.toConstantVal.type
--dbg_trace (← whnf c.toConstantVal.type).ctorName
--dbg_trace c.toConstantVal.type.ctorName
let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
let y := ← forallTelescopeReducing cTy fun arr _exp => do
  let pfs := ← arr.filterM isProof
  pfs.mapM (inferType ·)
return y

/-- `getPropsNonInst thm` is similar to `getProps thm`, but only returns a list of `Expr`essions
corresponding to hypotheses of the declaration with name `thm` that are `Prop`s. -/
def getPropsNonInst (thm : Name) : MetaM (List Expr) := do
let env := ← getEnv
let c := env.find? thm |>.get!
let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
let f := ← mkFreshExprMVar (some cTy)
let PropsAndImpls := ← f.mvarId!.withContext do
  let ctx := (← getLCtx).decls.toList.reduceOption.drop 1
  pure (ctx.map fun r : LocalDecl => (r.binderInfo, r.toExpr))
let nonInstProps := ← PropsAndImpls.mapM fun dc =>
  if dc.1 != .instImplicit then do
    let typ := ← inferType dc.2
    if isProp (← inferType typ) then
      pure (some typ)
    else pure none
  else pure none
return nonInstProps.reduceOption

--  consider using `getPropsNonInst` instead of `getProps`.
def getOneProp (thm : Name) : MetaM Expr := do
match ← getProps thm with
  | #[] => throwError "No `Prop` hipotheses found: is this a good `junk`-lemma?"
  | #[p] => pure p
  | y => do
    let str := ← y.mapM fun x => do
      let xx := (← ppExpr x).pretty
      (m!"@[junk {xx}]").toString
    let str := str.toList.intersperse ""
    throwError (m!"More than one `Prop` hypothesis found.\n" ++
      m!"Please provide the name of an hypothesis to `junk`, as in \n" ++ m!"{str}")

end Lean.Expr
