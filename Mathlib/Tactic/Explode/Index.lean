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

/-- Main method behind `#explode` command. -/
partial def explode (e : Expr) (si : Bool) (depth : Nat) (entries : Entries) : MetaM Entries :=
  match e.cleanupAnnotations with
  | .lam varName varType body binderInfo => do
    trace[explode] ".lam"
    Meta.withLocalDecl varName binderInfo varType.cleanupAnnotations fun arg => do
      let body := Expr.instantiate1 body.cleanupAnnotations arg
      let entries_1 := entries.add arg
        { type    := ← addMessageContext <| ← Meta.inferType arg
          line    := entries.size
          depth   := depth
          status  := if si then Status.sintro else Status.intro
          thm     := ← addMessageContext <| arg
          deps    := [] }

      let entries_2 ← explode body si (if si then depth else depth + 1) entries_1

      let entries_3 := entries_2.add e
        { type    := ← addMessageContext <| ← Meta.inferType e
          line    := entries_2.size
          depth   := depth
          status  := Status.lam
          thm     := if (← Meta.inferType e).isArrow then "→I" else "∀I"
          deps    := if si
            then [entries.size, entries_2.size - 1]
            else ← appendDep entries_2 arg (← appendDep entries_2 body []) }

      return entries_3
  | .app .. => do
    if !(← Meta.isProof e) then
      trace[explode] ".app - missed {e}"
      return entries
    trace[explode] ".app"

    -- If we stumbled upon an application `f a b c`,
    -- don't just parse this one application, `a; b; c; f a; (f a) b; ((f a) b) c`
    -- lump them all under a single line! `a; b; c; f a b c`
    let fn := Expr.getAppFn e
    let args := Expr.getAppArgs e

    -- We could turn this off iff it's a `.const`, but it's nice to have a theorem
    -- we're about to apply explicitly stated in the Fitch table
    let entries_1 ← explode fn false depth entries

    let mut entries_2 := entries_1
    let mut deps_3 := []
    for arg in args do
      entries_2 ← explode arg false depth entries_2
      deps_3 ← appendDep entries_2 arg deps_3
    deps_3 ← appendDep entries_1 fn deps_3.reverse

    let entries_3 := entries_2.add e
      { type    := ← addMessageContext <| ← Meta.inferType e
        line    := entries_2.size
        depth   := depth
        status  := Status.reg
        thm     := ← addMessageContext <| if fn.isConst then m!"{fn}()" else "∀E"
        deps    := deps_3 }

    return entries_3
  | .letE .. => do
    trace[explode] "auxilliary - strip .letE"
    explode (reduceLets e) si depth entries
  | .mdata _ expr => do
    trace[explode] "auxilliary - strip .mdata"
    explode expr si depth entries
  | _ => do
    -- Right now all of these are caught by the default case.
    -- Might be good to handle them separately.
    -- Expr.lit, Expr.forallE, Expr.const, Expr.sort, Expr.mvar, Expr.fvar, Expr.bvar
    trace[explode] "default - .{e.ctorName}"
    let entries := entries.add e
      { type    := ← addMessageContext <| ← Meta.inferType e
        line    := entries.size
        depth   := depth
        status  := Status.reg
        thm     := ← addMessageContext e
        deps    := [] }
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
elab "#explode " theoremStx:ident : command => do
  let theoremName : Name ← Elab.resolveGlobalConstNoOverloadWithInfo theoremStx
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!

  Elab.Command.liftCoreM do
    Meta.MetaM.run' do
      let results ← Mathlib.Explode.explode body true 0 default
      let fitchTable : MessageData ← Mathlib.Explode.entriesToMd results
      Lean.logInfo (theoremName ++ "\n\n" ++ fitchTable ++ "\n")
