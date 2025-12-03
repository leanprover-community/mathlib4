/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public meta import Lean.Elab.App
public meta import Lean.Util.CollectLevelParams
public meta import Mathlib.Lean.Elab.Term

open Lean Elab Term

declare_syntax_cat wildcard_universe

syntax "_" : wildcard_universe
syntax "*" : wildcard_universe
syntax level : wildcard_universe

syntax (name := wildcardUniverse)
    ident noWs ".!{" wildcard_universe,* "}" Parser.Term.argument* : term

inductive LevelWildcardKind where
  | mvar
  | param
  | explicit (l : Level)

meta def elabWildcardUniverses (us : Array Syntax) : TermElabM (Array LevelWildcardKind) := do
  us.mapM fun u =>
    match u with
    | `(wildcard_universe|_) => return .mvar
    | `(wildcard_universe|*) => return .param
    | `(wildcard_universe|$l:level) => do
      let lvl ← elabLevel l
      return .explicit lvl
    | _ => throwUnsupportedSyntax

meta def Lean.Level.getParams (l : Level) : List Name :=
  match l with
  | .param n => [n]
  | .mvar _ => []
  | .zero => []
  | .succ l' => l'.getParams
  | .max a b => a.getParams ++ b.getParams
  | .imax a b => a.getParams ++ b.getParams

@[term_elab wildcardUniverse]
meta def elabWildcardUniverseShort : TermElab := fun stx expectedType? => do
  match stx with
  | `($id:ident.!{$us,*} $args*) =>
    let constName ← Lean.resolveGlobalConstNoOverload id
    let constInfo ← Lean.getConstInfo constName
    let numLevels := constInfo.levelParams.length

    let mut levels ← elabWildcardUniverses us
    while levels.size < numLevels do
      levels := levels.push .mvar

    let constLevels : Array Level ← levels.mapM fun k => do
      match k with
      | .mvar => Meta.mkFreshLevelMVar
      | .param => mkFreshLevelParam
      | .explicit l => return l

    let fn : Expr := .const constName constLevels.toList

    let (namedArgs, args, ellipsis) ← expandArgs args

    let expr ← elabAppArgs fn namedArgs args expectedType?
      (explicit := false) (ellipsis := ellipsis)

    let constLevels ← constLevels.mapM Lean.instantiateLevelMVars
    let levelSpecWithLevel := levels.zip constLevels

    -- Collect all level params from the elaborated expression and its type
    let expr ← instantiateMVars expr
    let exprType ← Meta.inferType expr
    let exprParams := (collectLevelParams (collectLevelParams {} expr) exprType).params

    let mut levelNames ← getLevelNames

    for ((k, l), idx) in levelSpecWithLevel.zipIdx do
      unless k matches .param do continue
      let .param name := l | continue
      -- Collect level params from later universe arguments
      let laterLevels := constLevels.toList.drop (idx + 1)
      let laterParams := laterLevels.flatMap Level.getParams
      -- Also include all level params from the expression (arguments) that aren't our fresh param
      let allLaterParams := (laterParams ++ exprParams.toList).filter (· != name)
      let levelNames' := levelNames.filter (· != name)
      let mut lastIdx : Option Nat := none
      for (n, i) in levelNames'.zipIdx do
        if allLaterParams.contains n then
          lastIdx := some i
      levelNames := match lastIdx with
        | some pos => levelNames'.insertIdx (pos + 1) name
        | none => name :: levelNames'

    setLevelNames levelNames

    pure expr
  | _ => throwUnsupportedSyntax
