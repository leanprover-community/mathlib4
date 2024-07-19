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
If `stx` is a nameless instance, then it also tries to fetch the `ident` for the instance.
Otherwise it returns `.missing`. -/
def getId (stx : Syntax) : CommandElabM Syntax := do
  -- If the command contains a `declId`, we use the implied `ident`.
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      -- Otherwise, the command could be a nameless `instance`.
      match stx.find? (·.isOfKind ``Lean.Parser.Command.instance) with
        | none => return .missing
        | some stx => do
          -- if it is a nameless `instance`, we retrieve the autogenerated name
          let dv ← mkDefViewOfInstance {} stx
          return dv.declId[0]

/-- `getIds stx` extracts all identifiers, collecting them in a `NameSet`. -/
partial
def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- `getAttrNames stx` extracts `attribute`s from `stx`.
It does not collect `simp`, `ext`, `to_additive`.
It should collect almost all other attributes, e.g., `fun_prop`. -/
def getAttrNames (stx : Syntax) : NameSet :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

/-- `getAttrs env stx` returns all attribute declaration names contained in `stx` and registered
in the `Environment `env`. -/
def getAttrs (env : Environment) (stx : Syntax) : NameSet :=
  Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

/--`getAllImports cmd id` takes a `Syntax` input `cmd` and returns the `NameSet` of all the
module names that are implied by
* the `SyntaxNodeKinds`,
* the attributes of `cmd` (if there are any),
* the identifiers contained in `cmd`,
* if `cmd` adds a declaration `d` to the environment, then also all the module names implied by `d`.
The argument `id` is expected to be an identifier.
It is used either for the internally generated name of a "nameless" `instance` or when parsing
an identifier representing the name of a declaration.
-/
def getAllImports (cmd id : Syntax) (dbg? : Bool := false) :
    CommandElabM NameSet := do
  let env ← getEnv
  let id1 ← getId cmd
  let nm ← (liftCoreM do realizeGlobalConstNoOverload id1 <|> return default)
  -- We collect the implied declaration names, the `SyntaxNodeKinds` and the attributes.
  let ts := getVisited env nm
              |>.append (getVisited env id.getId)
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
      let new := match env.getModuleIdxFor? t with
        | some t => (hm.find? t).get!
        | none   => .anonymous --instead of `getMainModule`, we omit the current module
        if !fins.contains new then fins := fins.insert new
  return fins.erase .anonymous

/-- `getIrredundantImports env importNames` takes an `Environment` and a `NameSet` as inputs.
Assuming that `importNames` are module names,
it returns the `NameSet` consisting of a minimal collection of module names whose transitive
closure is enough to parse (and elaborate) `cmd`. -/
def getIrredundantImports (env : Environment) (importNames : NameSet) : NameSet :=
  importNames.diff (env.findRedundantImports importNames.toArray)

/-- `minImpsCore stx id` is the internal function to elaborate the `#min_imports in` command.
It collects the irredundant imports to parse and elaborate `stx` and logs
```lean
import A
import B
...
import Z
```
The `id` input is expected to be the name of the declaration that is currently processed.
It is used to provide the internally generated name for "nameless" `instance`s.
-/
def minImpsCore (stx id : Syntax) : CommandElabM Unit := do
    let tot := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let fileNames := tot.toArray.qsort Name.lt
    --let fileNames := if tk.isSome then (fileNames).filter (`Mathlib).isPrefixOf else fileNames
    logInfoAt (← getRef) m!"{"\n".intercalate (fileNames.map (s!"import {·}")).toList}"

/-- `#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by elaborating `cmd`
to find a collection of minimal imports that should be sufficient for `cmd` to work. -/
syntax (name := minImpsStx) "#min_imports in" command : command

@[inherit_doc minImpsStx]
syntax "#min_imports in" term : command

elab_rules : command
  | `(#min_imports in $cmd:command) => do
    -- In case `cmd` is a "nameless" `instance`, we produce its name.
    -- It is important that this is collected *before* adding the declaration to the environment,
    -- since `getId` probes the name-generator using the current environment: if the declaration
    -- were already present, `getId` would return a new name that does not clash with it!
    let id ← getId cmd
    Elab.Command.elabCommand cmd <|> pure ()
    minImpsCore cmd id
  | `(#min_imports in $cmd:term) => minImpsCore cmd cmd

end Mathlib.Command.MinImports
