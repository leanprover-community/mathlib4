/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports

/-! # `#min_imps` a command to find minimal imports

`#min_imps cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work.

Unlike the related `#find_home`, this command takes into account notation and tactic information.
-/

open Lean Elab Command

namespace Mathlib.Command.MinImps

/-- `getSyntaxNodeKinds stx` takes a `Syntax` input `stx` and returns the `NameSet` of all the
`SyntaxNodeKinds` and all the identifiers contained in `stx`. -/
partial
def getSyntaxNodeKinds : Syntax → NameSet
  | .node _ kind args =>
    ((args.map getSyntaxNodeKinds).foldl (NameSet.append · ·) {}).insert kind
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- extracts the names of the declarations in `env` on which `decl` depends. -/
-- source:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Counting.20prerequisites.20of.20a.20theorem/near/425370265
def getVisited (env : Environment) (decl : Name) : NameSet :=
  let (_, { visited, .. }) := CollectAxioms.collect decl |>.run env |>.run {}
  visited

def getDeclId (stx : Syntax) : Syntax :=
  (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).getD default

def getId (stx : Syntax) : Syntax :=
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => declId[0]
    | none => stx

/--`getSyntaxImports cmd` takes a `Syntax` input `cmd` and returns the `NameSet` of all the
module names that are implied by the `SyntaxNodeKinds` and the identifiers contained in `cmd`. -/
def getSyntaxImports {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m]
    [MonadQuotation m] (cmd : Syntax) (dbg? : Bool := false) :
    m NameSet := do
  let env ← getEnv
  --let nm ← liftCoreM do realizeGlobalConstNoOverloadWithInfo (getId cmd)
  let ts := (getSyntaxNodeKinds cmd).append <| getVisited env (getId cmd).getId
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.insert ((env.getModuleIdx? imp).getD default) imp
  let mut fins : NameSet := {}
  for t1 in ts do
    let tns := t1::(← resolveGlobalName t1).map Prod.fst
    for t in tns do
      let new := ← match env.getModuleIdxFor? t with
        | some t => return (hm.find? t).get!
        | none   => return default --getMainModule
        if !fins.contains new then fins := fins.insert new
  return fins

/-
def importTips (ns : NameSet) : CommandElabM NameSet := do
  let all := (← getEnv).allImportedModuleNames
  dbg_trace ← getBuildDir
  dbg_trace ← getLibDir ""
  let allFileNames := all.map (modToFilePath "." · "lean")
  dbg_trace allFileNames
  let importDatas ← allFileNames.mapM fun n => return (← readModuleData n).1
  dbg_trace importDatas.map fun i => i.imports
  return ns

run_cmd
  let _ ← importTips <| (NameSet.empty).insert `Mathlib.Init.Data.Nat.Basic
-/

def getAllImports {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m] [MonadQuotation m]
    (stx : Syntax) : m NameSet := do
  let env ← getEnv
  let exprImports := {} --← match cmd.raw.find? (·.isOfKind ``Lean.Parser.Command.declId) with
                     -- | none => return .empty
                     -- | some declId => liftCoreM do
                     --   (← realizeGlobalConstNoOverloadWithInfo declId[0]).findHome (some env)
  let fins ← getSyntaxImports stx --true
  let mut tot := (fins.append exprImports).erase default
  let redundant := env.findRedundantImports tot.toArray
  for n in redundant do
    tot := tot.erase n
  return tot

def minImpsCore (stx : Syntax) : CommandElabM Unit := do
    let tot ← getAllImports stx
    let fileNames := tot.toArray.qsort Name.lt
    --let fileNames := if tk.isSome then (fileNames).filter (`Mathlib).isPrefixOf else fileNames
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"

/-- `#min_imps cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work. -/
syntax (name := minImpsStx) "#min_imps" command : command

@[inherit_doc minImpsStx]
syntax "#min_imps" term : command

elab_rules : command
  | `(#min_imps $cmd:command)=> do
    Elab.Command.elabCommand cmd <|> pure ()
    minImpsCore cmd
  | `(#min_imps $cmd:term)=> minImpsCore cmd

end Mathlib.Command.MinImps
