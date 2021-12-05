/-
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
import Lean.Elab.SyntheticMVars
import Mathlib.Util.TermUnsafe

namespace Mathlib.RunTac
open Lean Elab Term Meta

unsafe def evalExpr (α) (expectedType : Expr) (value : Expr) (safety := DefinitionSafety.unsafe) : MetaM α :=
  withoutModifyingEnv do
    let name ← mkFreshUserName `_tmp
    let type ← inferType value
    unless ← isDefEq type expectedType do
      throwError "unexpected type at evalExpr: {type} ≠ {expectedType}"
    let decl := Declaration.defnDecl {
       name, levelParams := [], type, safety, value
       hints := ReducibilityHints.opaque
    }
    addAndCompile decl
    evalConst α name

unsafe def evalTerm (α) (type : Expr) (value : Syntax) (safety := DefinitionSafety.unsafe) : TermElabM α := do
  let v ← Term.elabTermEnsuringType value type
  synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  if ← logUnassignedUsingErrorInfos (← getMVars v) then throwAbortTerm
  evalExpr α type v safety

open Tactic in
elab "runTac" e:doSeq : tactic => do
  ← unsafe evalTerm (TacticM Unit) (mkApp (mkConst ``TacticM) (mkConst ``Unit))
    (← `(discard do $e))
