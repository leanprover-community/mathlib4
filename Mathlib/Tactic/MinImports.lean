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

namespace Mathlib.Command.MinImports

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

/-- extract all identifiers, as a `NameSet`. -/
partial
def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- misses `simp`, `ext`, `to_additive`.  Catches `fun_prop`... -/
def getAttrNames (stx : Syntax) : NameSet :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

/-- returns all attribute declaration names -/
def getAttrs (env : Environment) (stx : Syntax) : NameSet :=
  Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do --.filterMap fun attr =>
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

/--`getAllImports cmd` takes a `Syntax` input `cmd` and returns the `NameSet` of all the
module names that are implied by the `SyntaxNodeKinds` and the identifiers contained in `cmd`. -/
def getAllImports {m : Type → Type} [Monad m] [MonadResolveName m] [MonadEnv m]
    (cmd : Syntax) (dbg? : Bool := false) :
    m NameSet := do
  let env ← getEnv
  --let nm ← liftCoreM do realizeGlobalConstNoOverloadWithInfo (getId cmd)
  -- we put together the implied declaration names, the `SyntaxNodeKinds`, the attributes
  let ts := getVisited env (getId cmd).getId
              |>.append (getSyntaxNodeKinds cmd)
              |>.append (getAttrs env cmd)
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

/-- `minImportsCore stx` is the internal function to elaborate the `#min_imports in` command.
It collects the irredundant imports to parse and elaborate `stx` and logs
```lean
import A
import B
...
import Z
```
 -/
def minImportsCore (stx : Syntax) : CommandElabM Unit := do
    let tot ← getIrredundantImports stx
    let fileNames := tot.toArray.qsort Name.lt
    --let fileNames := if tk.isSome then (fileNames).filter (`Mathlib).isPrefixOf else fileNames
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"

/-- `#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work.

The variant
```
#min_imports start
[multiple commands]
until
```
does a similar thing, but reports minimal imports for all the commands between
`#min_imports start` and `until`.
The `until` is optional: if it is missing, then `#min_imports start` will report the combined
minimal imports for every command until the end of the file.
-/
syntax (name := minImportsStx) "#min_imports in" command : command

@[inherit_doc minImportsStx]
syntax "#min_imports in" term : command

elab_rules : command
  | `(#min_imports in $cmd:command)=> do
    Elab.Command.elabCommand cmd <|> pure ()
    minImportsCore cmd
  | `(#min_imports in $cmd:term)=> minImportsCore cmd

@[inherit_doc minImportsStx]
syntax "#min_imports start" command* "until"? : command

elab_rules : command
  | `(#min_imports start $cmds* $[until]?)=> do
    let mut tot : NameSet := {}
    for cmd in cmds do
      Elab.Command.elabCommand cmd <|> pure ()
      tot := tot.append (← getIrredundantImports cmd)
    let fileNames := tot.toArray.qsort Name.lt
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"

end Mathlib.Command.MinImports

/-!
#  The "minImports" linter

The "minImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/-- `minImportsRef` keeps track of cumulative imports across multiple commands. -/
initialize minImportsRef : IO.Ref NameSet ← IO.mkRef {}

/-- `#reset_min_imports` sets to empty the current list of cumulative imports. -/
elab "#reset_min_imports" : command => minImportsRef.set {}

/-- The "minImports" linter tracks information about minimal imports over several commands. -/
register_option linter.minImports : Bool := {
  defValue := false
  descr := "enable the minImports linter"
}

namespace MinImports

open Mathlib.Command.MinImports

/-- Gets the value of the `linter.minImports` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.minImports o

@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where
  run := withSetOptionIn fun stx => do
    let prevImports ← minImportsRef.get
    unless linter.minImports.get (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if stx.isOfKind ``Parser.Command.eoi then logInfo m!"{(← getEnv).imports.map (·.module)}"
    let newImports ← getIrredundantImports stx
    let tot := newImports.append prevImports
    let redundant := (← getEnv).findRedundantImports (prevImports.append tot).toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if (currImpArray != #[] && currImpArray != #[`Lean.Parser.Command]) &&
       currImpArray ≠ prevImports.toArray.qsort Name.lt then
      minImportsRef.modify fun _ => currImports
      Linter.logLint linter.minImports stx
        m!"Imports increased to\n{currImpArray}"

initialize addLinter minImportsLinter

end MinImports
