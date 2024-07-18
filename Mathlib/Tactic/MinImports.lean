/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports

/-! # `#min_imports in` a command to find minimal imports

`#min_imports in stx` scans the syntax `stx` to find a collection of minimal imports that should be
sufficient for `stx` to make sense.
If `stx` is a command, then it also elaborates `stx` and, in case it is a declaration, then
it also finds the imports implied by the declaration.

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

/-- `getId stx` takes as input a `Syntax` `stx`.
If `stx` contains a `declId`, then it returns the `ident`-syntax for the `declId`.
Otherwise it returns `stx` itself. -/
def getId (stx : Syntax) : Syntax :=
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => declId[0]
    | none => stx

/--`getAllImports cmd` takes a `Syntax` input `cmd` and returns the `NameSet` of all the
module names that are implied by the `SyntaxNodeKinds` and the identifiers contained in `cmd`. -/
def getAllImports {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m]
    (cmd : Syntax) (dbg? : Bool := false) :
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

/-- `getIrredundantImports cmd` takes a `Syntax` input `cmd`.
It returns the `NameSet` consisting of a minimal collection of module names whose transitive
closure is enough to parse (and elaborate) `cmd`. -/
def getIrredundantImports {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m]
    (stx : Syntax) : m NameSet := do
  let env ← getEnv
  let fins ← getAllImports stx --true
  let mut tot := fins.erase default
  let redundant := env.findRedundantImports tot.toArray
  return tot.diff redundant

/-- `minImpsCore stx` is the internal function to elaborate the `#min_imports in` command.
It collects the irredundant imports to parse and elaborate `stx` and logs
```lean
import A
import B
...
import Z
```
 -/
def minImpsCore (stx : Syntax) : CommandElabM Unit := do
    let tot ← getIrredundantImports stx
    let fileNames := tot.toArray.qsort Name.lt
    --let fileNames := if tk.isSome then (fileNames).filter (`Mathlib).isPrefixOf else fileNames
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"

/-- `#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work. -/
syntax (name := minImpsStx) "#min_imports in" command : command

@[inherit_doc minImpsStx]
syntax "#min_imports in" term : command

elab_rules : command
  | `(#min_imports in $cmd:command)=> do
    Elab.Command.elabCommand cmd <|> pure ()
    minImpsCore cmd
  | `(#min_imports in $cmd:term)=> minImpsCore cmd

end Mathlib.Command.MinImps
