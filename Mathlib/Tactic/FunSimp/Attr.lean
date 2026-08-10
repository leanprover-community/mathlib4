/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Tactic.Translate.Attributes

/-!
# Implementation of the `@[fun_simp]` attribute
-/

public meta section

namespace Mathlib.Tactic.FunSimp

open Lean Meta Elab Parser.Tactic Simp

/-- Simp extension used by `fun_simp`. -/
initialize simpExt : SimpExtension ← mkSimpExt `fun_simp
initialize simpExtensionMapRef.modify fun map => map.insert `fun_simp simpExt

/-- Simproc extension used by `fun_simp`. -/
initialize simprocExt : SimprocExtension ← registerSimprocAttr `fun_simp_proc "fun_simp_proc" none
@[nolint docBlame]
syntax (name := Parser.Attr.fun_simp_proc)
  "fun_simp_proc" (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? : attr

/-- Environment extension storing the mapping from lemmas to their preprocessed form. -/
initialize auxThmExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn nameMap entry := nameMap.insert entry.1 entry.2
    addImportedFn _ := {}
  }

initialize registerTraceClass `fun_simp.attr

/-- Moves the free variables at the end of the LHS to the RHS, e.g. `f x y = x + y` becomes
`f = fun x y => x + y`. Returns `some (type, proof)`, or `none` when no free variables can be moved.
-/
def removeArgs (type proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut proof := proof
  let mut (_, lhs, rhs) := type.eq?.get!
  let mut argRemoved := false
  let mut ctx := (← getLCtx).getFVars
  repeat
    let .app f x := lhs | break
    let some xId := x.fvarId? | break
    unless (← xId.getBinderInfo).isExplicit do break
    if f.containsFVar xId then break
    if ← ctx.anyM (fun y => do return (← y.fvarId!.getType).containsFVar xId) then break
    ctx := ctx.erase x
    lhs := f
    rhs := (← mkLambdaFVars #[x] rhs).eta
    proof ← mkFunExt (← mkLambdaFVars #[x] proof)
    argRemoved := true
  if argRemoved then
    return some (← mkForallFVars ctx (← mkEq lhs rhs), ← mkLambdaFVars ctx proof)
  return none

/-- Coerces both sides of an equality to functions. Returns `some (type, proof)`, or `none` if this
is not possible. -/
def applyCoeFun (type proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let (eqType, lhs, rhs) := type.eq?.get!
  let u ← getLevel eqType
  let v ← mkFreshLevelMVar
  let γ ← mkFreshExprMVar (← mkArrow eqType (mkSort v))
  let .some inst ← trySynthInstance (mkApp2 (.const ``CoeFun [u,v]) eqType γ)
  | return none
  let coe ← instantiateMVars (mkApp3 (.const ``CoeFun.coe [u,v]) eqType γ inst)
  let (lhs, _) ← expandCoe (.app coe lhs)
  let (rhs, _) ← expandCoe (.app coe rhs)
  let ctx := (← getLCtx).getFVars
  return some (← mkForallFVars ctx (← mkEq lhs rhs), ← mkLambdaFVars ctx (← mkCongrArg coe proof))

/-- Applies preprocessing steps to an equality of functions. Returns `some (type, proof)`, or
`none` if no preprocessing is needed. -/
def preprocess (declName : Name) (inv : Bool) : MetaM (Option (Expr × Expr)) :=
  withReducible do
    let info ← getConstInfo declName
    forallTelescopeReducing info.type fun args type => do
      let mut type := type
      let mut proof := mkAppN (← mkConstWithLevelParams declName) args
      unless type.isEq do
        throwError m!"The type of {.ofConstName declName} is not an equality"
      if inv then
        let (_, lhs, rhs) := type.eq?.get!
        type ← mkEq rhs lhs
        proof ← mkEqSymm proof
      if let some res ← removeArgs type proof then return some res
      if let some (.forallE .., _, _) := type.eq? then
        return if inv then some (type, proof) else none
      if let some res ← applyCoeFun type proof then return some res
      throwError m!"The type of {.ofConstName declName} is not an equality of functions"

/-- Preprocess and add a theorem tagged with `@[fun_simp]` to the simp set. Returns the list of
auxiliary lemmas generated. -/
partial def addThm (declName : Name) (post inv : Bool) (attrKind : AttributeKind) (prio : Nat) :
    MetaM (Array Name) := do
  if let some projInfo ← getProjectionFnInfo? declName then
    if projInfo.fromClass then
      -- Allow tagging class fields such as `HasUncurry.uncurry`
      simpExt.add <| .toUnfold declName
      return #[]
  match ← getEqnsFor? declName with
  | some eqns => eqns.flatMapM (addThm · post inv attrKind prio)
  | none =>
    let (simpThm, isAux) ←
      match auxThmExt.getState (← getEnv) |>.get? declName with
      | some auxThm =>
        trace[fun_simp.attr]
          m!"Auxiliary lemma {.ofConstName auxThm} for {.ofConstName declName} already generated"
        pure (auxThm, true)
      | none =>
        let some (type, proof) ← preprocess declName inv |
          trace[fun_simp.attr] m!"No preprocessing needed for {.ofConstName declName}"
          pure (declName, false)
        let auxThm ←
          mkAuxLemma (← getConstInfo declName).levelParams type proof `_fun_simp
        trace[fun_simp.attr]
          m!"Generated auxiliary lemma {.ofConstName auxThm} for {.ofConstName declName}"
        modifyEnv (auxThmExt.addEntry · (declName, auxThm))
        pure (auxThm, true)
    addSimpTheorem simpExt simpThm post (inv := false) attrKind prio
    return if isAux then #[simpThm] else #[]

/-- Elaboration of the `@[fun_simp]` attribute. Returns the list of auxiliary lemmas generated. -/
def addAttr (declName : Name) (stx : Syntax) (attrKind : AttributeKind) : AttrM (Array Name) := do
  let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
  let inv := !stx[2].isNone
  let prio ← getAttrParamOptPrio stx[3]
  MetaM.run' <| addThm declName post inv attrKind prio

/-- Remove a theorem from the simp set. -/
partial def eraseThm (declName : Name) : MetaM Unit := do
  let isClassProj :=
    match ← getProjectionFnInfo? declName with
    | some projInfo => projInfo.fromClass
    | none => false
  let eqns ← if isClassProj then pure none else getEqnsFor? declName
  match eqns with
  | some eqns => eqns.forM eraseThm
  | none =>
    let auxThm := auxThmExt.getState (← getEnv) |>.getD declName declName
    let s := simpExt.getState (← getEnv)
    let s ← s.erase (.decl auxThm)
    modifyEnv fun env => simpExt.modifyState env fun _ => s

/--
Attribute for tagging lemmas used by the `fun_simp` tactic. Has the same options as the `@[simp]`
attribute.
-/
syntax (name := funSimpAttr)
  "fun_simp" (simpPre <|> simpPost)? unicode("← ", "<- ")? (prio)? : attr

initialize registerBuiltinAttribute {
  name := `funSimpAttr
  descr := "Attribute for tagging lemmas used by the `fun_simp` tactic."
  add declName stx attrKind := discard <| addAttr declName stx attrKind
  erase declName := MetaM.run' <| eraseThm declName
}

initialize registerGeneratingAttr `funSimpAttr addAttr

end Mathlib.Tactic.FunSimp
