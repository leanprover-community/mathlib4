/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus
-/
import Lean
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty

/-!
# Explode command

This file contains the main code behind the `#explode` command.
If you have a theorem with a name `hi`, `#explode hi` will display a Fitch table.
-/

set_option linter.unusedVariables false
open Lean

namespace Mathlib.Explode

/-- Prepend the `line` of the `Entry` to `deps` if it's not `none`. -/
def consDep (entry? : Option Entry) (deps : List (Option Nat)) : List (Option Nat) :=
  entry?.map Entry.line! :: deps

/-- Core `explode` algorithm.

- `filter` is a condition for which expressions to process
- `e` is the expression to process
- `depth` is the current abstraction depth
- `entries` is the table so far
- `start` is whether we are at the top-level of the expression, which
  causes lambdas to use `Status.sintro` to prevent a layer of nesting.
-/
partial def explode_core (filter : Expr → MetaM Bool) (e : Expr)
    (depth : Nat) (entries : Entries) (start : Bool := false) :
    MetaM (Option Entry × Entries) := do
  let e := e.cleanupAnnotations
  if let some entry := entries.find? e then
    return (entry, entries)
  if !(← filter e) then
    trace[explode] "filtered out {e}"
    return (none, entries)
  match e with
  | .lam .. => do
    trace[explode] ".lam"
    Meta.lambdaTelescope e fun args body => do
      let mut entries' := entries
      let mut rdeps := []
      for arg in args, i in [0:args.size] do
        let (argEntry?, entries'') := entries'.add arg
          { type    := ← addMessageContext <| ← Meta.inferType arg
            depth   := depth
            status  :=
              if start
              then Status.sintro
              else if i == 0 then Status.intro else Status.cintro
            thm     := ← addMessageContext <| arg
            deps    := [] }
        entries' := entries''
        rdeps := consDep argEntry? rdeps
      let (bodyEntry?, entries) ←
        explode_core filter body (if start then depth else depth + 1) entries'
      rdeps := consDep bodyEntry? rdeps
      let (entry, entries) := entries.add e
        { type    := ← addMessageContext <| ← Meta.inferType e
          depth   := depth
          status  := Status.lam
          thm     := "∀I" -- TODO use "→I" if it's purely implications?
          deps    := rdeps.reverse }
      return (entry, entries)
  | .app .. => do
    trace[explode] ".app"

    -- We want to represent entire applications as a single line in the table
    let fn := Expr.getAppFn e
    let args := Expr.getAppArgs e

    -- If the function is a `const`, then it's not local so we do not need an
    -- entry in the table for it. We store the theorem name in the `thm` field
    -- below, giving access to the theorem's type on hover in the UI.
    -- Whether to include the entry could be controlled by a configuration option.
    let (fnEntry?, entries) ←
      if fn.isConst then
        pure (none, entries)
      else
        explode_core filter fn depth entries
    let deps := if fn.isConst then [] else consDep fnEntry? []

    let mut entries' := entries
    let mut rdeps := []
    for arg in args do
      let (appEntry?, entries'') ← explode_core filter arg depth entries'
      entries' := entries''
      rdeps := consDep appEntry? rdeps
    let deps := deps ++ rdeps.reverse

    let (entry, entries) := entries'.add e
      { type    := ← addMessageContext <| ← Meta.inferType e
        depth   := depth
        status  := Status.reg
        thm     := ← addMessageContext <| if fn.isConst then fn else "∀E"
        deps    := deps }
    return (entry, entries)
  | .letE varName varType val body _ => do
    trace[explode] ".letE"
    let varType := varType.cleanupAnnotations
    Meta.withLocalDeclD varName varType fun var => do
      let (valEntry?, entries) ← explode_core filter val depth entries
      -- Add a synonym so that the substituted fvars refer to `valEntry?`
      let entries := valEntry?.map (entries.addSynonym var) |>.getD entries
      explode_core filter (body.instantiate1 var) depth entries
  | _ => do
    -- Right now all of these are caught by this case case:
    --   Expr.lit, Expr.forallE, Expr.const, Expr.sort, Expr.mvar, Expr.fvar, Expr.bvar
    --   (Note: Expr.mdata is stripped by cleanupAnnotations)
    -- Might be good to handle them individually.
    trace[explode] "default - .{e.ctorName}"
    handleDefault e entries
where
  handleDefault (e : Expr) (entries : Entries) : MetaM (Option Entry × Entries) := do
    let (entry, entries) := entries.add e
      { type    := ← addMessageContext <| ← Meta.inferType e
        depth   := depth
        status  := Status.reg
        thm     := ← addMessageContext e
        deps    := [] }
    return (entry, entries)

/-- Main definition behind `#explode` command. -/
def explode (e : Expr) (filterProofs : Bool := true) : MetaM Entries := do
  let filter (e : Expr) : MetaM Bool :=
    if filterProofs then Meta.isProof e else return true
  let (_, entries) ← explode_core (start := true) filter e 0 default
  return entries

end Mathlib.Explode

/--
`#explode decl_name` displays a proof term in a line-by-line format somewhat akin to a Fitch-style
proof or the Metamath proof style.

For example, exploding the following theorem:

```lean
theorem application : True ∧ True :=
  And.intro True.intro True.intro
#explode application
```

produces:

```lean
iff_true_intro : ∀ {a : Prop}, a → (a ↔ true)
0│         │ @And.intro  │ ∀ {a b : Prop}, a → b → a ∧ b
1│         │ True        │ Prop
2│         │ True.intro  │ True
3│0,1,1,2,2│ And.intro() │ True ∧ True
```

## Overview

Given a body of a theorem, we parse it as an `Expr`.
We only have 3 cases (written in pseudocode):
  - `Expr.lam` - displays `fun x => y` as
    ```lean
     |    | x        -- (X)
     |    | y        -- (Y)
     | →I | fun x => y -- (X → Y)
    ```
  - `Expr.app` - displays `f a b c` as
     ```lean
     |    | f       -- (A → B → C → D)
     |    | a       -- (A)
     |    | b       -- (B)
     |    | c       -- (C)
     | →E | f a b c -- (D)
     ```
  - everything else (constants, fvars, potential weird things) - displays `x` as `x`.

## In more details

The output of `#explode` is a Fitch-style proof in a four-column diagram modeled after Metamath
proof displays like [this](http://us.metamath.org/mpeuni/ru.html). The headers of the columns are
"Step", "Hyp", "Ref", "Type" (or "Expression" in the case of Metamath):
* **Step**: An increasing sequence of numbers for each row in the proof.
* **Hyp**: The **Step**s we used to create this row.
* **Ref**: The name of the theorem being applied. This is well-defined in Metamath, but in Lean
  there are some special steps that may have long names because the structure of proof terms doesn't
  exactly match this mold. For example, **Ref** can be `theoremName()` (same as `∀E`, but we know
  the theorem name), `∀E`, `→I`, or `∀I`.
* **Type**: This contains the type of the proof term, the theorem being proven at the current step.

Also, it is common for a Lean theorem to begin with a sequence of lambdas introducing local
constants of the theorem. In order to minimize the indentation level, the `∀I` steps at the end of
the proof will be introduced in a group and the indentation will stay fixed. (The indentation
brackets are only needed in order to delimit the scope of assumptions, and these assumptions
have global scope anyway so detailed tracking is not necessary.)
-/
elab "#explode " theoremStx:ident : command => Elab.Command.liftTermElabM do
  let theoremName : Name ← Elab.resolveGlobalConstNoOverloadWithInfo theoremStx
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  let entries ← Mathlib.Explode.explode body
  let fitchTable : MessageData ← Mathlib.Explode.entriesToMessageData entries
  Lean.logInfo (theoremName ++ "\n\n" ++ fitchTable ++ "\n")
