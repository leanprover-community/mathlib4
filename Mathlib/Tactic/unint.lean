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
#check getMainGoal
#check withMVarContext
#check getLocalDecl
#check MVarId.withContext
/-- `getPropsNonInst thm` is similar to `getProps thm`, but only returns a list of `Expr`essions
corresponding to hypotheses of the declaration with name `thm` that are `Prop`s. -/
def getPropsNonInst (thm : Name) : TacticM (List Expr) := do
let env := ← getEnv
let c := env.find? thm |>.get!
let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
let f := ← mkFreshExprMVar (some cTy)
--let r := ← f.mvarId!.withContext do
let _gs := ← getGoals
setGoals [f.mvarId!]
withMainContext do
let ctx := (← getLCtx).decls.toList.reduceOption.drop 1
--let ctx := getLocalDecl f.mvarId!
let PropsAndImpls := --← f.mvarId!.withContext do
  --let myCtx := ← f.mvarId!.getDecl
  --let ldcls := myCtx.lctx
  --let ctx := ldcls.decls.toList.reduceOption.drop 1
  (ctx.map fun r : LocalDecl => (r.binderInfo, r.toExpr))
let nonInstProps := ← PropsAndImpls.mapM fun dc =>
  if dc.1 != .instImplicit then do
    let typ := ← inferType dc.2
    if isProp (← inferType typ) then
      pure (some typ)
    else pure none
  else pure none
return nonInstProps.reduceOption
--pure r
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

#check Expr.find?
#check Expr.getUsedConstants
#check Expr.find?

--def getLocalConstants : Expr → MetaM (List Expr)
--  | bvar (deBruijnIndex : Nat) => pure []
--  | fvar (fvarId : FVarId) => pure []
--  | mvar (mvarId : MVarId) => pure []
--  | sort (u : Level) => pure []
--  | const (declName : Name) (us : List Level) => pure []
--  | app (fn : Expr) (arg : Expr) => pure []
--  | lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) => pure []
--  | forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo) => pure []
--  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool) => pure []
--  | mdata (data : MData) (expr : Expr) => pure []
--  | proj (typeName : Name) (idx : Nat) (struct : Expr) => pure []
--  | _ => pure []
--  | lit => pure []
set_option autoImplicit false
--#check revert
partial
def revertables : TacticM (List LocalDecl × MVarId) := do
  let ctx := (← getLCtx).decls.toList.reduceOption.drop 1
  let gMVar := ← getMainGoal
  let goal := ← getMainTarget
--  let foundExprs := (ctx.map fun x => goal.find? (. == x.toExpr)).reduceOption
  let foundDecls := (ctx.map fun x =>
    if (goal.find? (. == x.toExpr)).isSome then some x else none).reduceOption
--  logInfo m!"fex{foundExprs}"
  let fvarIdFound := (foundDecls.map Lean.LocalDecl.fvarId).toArray
  let (fvs, newGoal) := ← gMVar.revert fvarIdFound
  setGoals [newGoal]
  if fvs.size == 0 then pure (ctx, newGoal) else
    --dbg_trace f!"{fvs.map FVarId.name}"
    revertables
  --let (fvs, mvs) := Array.unzip x
  --dbg_trace x
--  let l := match goal with
--    | (.app fn arg)    => []
--    | m::ms => []

--  dbg_trace goal.getUsedConstants
  --let used := ctx.map

--/-
#check intros
#check Expr.getForallBinderNames
#check clear


def clearExtern : TacticM Unit := do
  let (dcls, goal) := ← Lean.Expr.revertables
  let newGoal ← goal.tryClearMany (dcls.map LocalDecl.fvarId).toArray
  setGoals [newGoal]
  let nms := Expr.getForallBinderNames (← getMainTarget)
  let (_newfvs, rGoal) := ← Lean.Meta.introNCore newGoal nms.length [] True True
  setGoals [rGoal]
--  _
--/

elab "clear_" : tactic => do
  let _ := ← Lean.Expr.revertables
  clearExtern

end Lean.Expr

example {α} [Add α] {e f : α} {a b d : Nat} {h : e ≠ f} (h₁ : a = b) {c : Int} : a + 5 = c ∨ True := by
  clear_
  run_tac do
    let _ := ← Lean.Expr.revertables
    Lean.Expr.clearExtern
  sorry
  --intros
  --exact Or.inr trivial
  --  let _ := ← Lean.Expr.revertables
