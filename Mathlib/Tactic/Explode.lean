/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Evgenia Karunus, Kyle Miller
-/
import Lean.Elab.Command
import Lean.PrettyPrinter
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

variable (select : Expr → MetaM Bool) (includeAllDeps : Bool) in
/-- Core `explode` algorithm.

- `select` is a condition for which expressions to process
- `includeAllDeps` is whether to include dependencies even if they were filtered out.
  If `True`, then `none` is inserted for omitted dependencies
- `e` is the expression to process
- `depth` is the current abstraction depth
- `entries` is the table so far
- `start` is whether we are at the top-level of the expression, which
  causes lambdas to use `Status.sintro` to prevent a layer of nesting.
-/
partial def explodeCore (e : Expr) (depth : Nat) (entries : Entries) (start : Bool := false) :
    MetaM (Option Entry × Entries) := do
  trace[explode] "depth = {depth}, start = {start}, e = {e}"
  let e := e.cleanupAnnotations
  if let some entry := entries.find? e then
    trace[explode] "already seen"
    return (entry, entries)
  if !(← select e) then
    trace[explode] "filtered out"
    return (none, entries)
  match e with
  | .lam .. => do
    trace[explode] ".lam"
    Meta.lambdaTelescope e fun args body => do
      let mut entries' := entries
      let mut rdeps := []
      for arg in args, i in [0:args.size] do
        let (argEntry, entries'') := entries'.add arg
          { type     := ← addMessageContext <| ← Meta.inferType arg
            depth    := depth
            status   :=
              if start
              then Status.sintro
              else if i == 0 then Status.intro else Status.cintro
            thm      := ← addMessageContext <| arg
            deps     := []
            useAsDep := ← select arg }
        entries' := entries''
        rdeps := some argEntry.line! :: rdeps
      let (bodyEntry?, entries) ←
        explodeCore body (if start then depth else depth + 1) entries'
      rdeps := consDep bodyEntry? rdeps
      let (entry, entries) := entries.add e
        { type     := ← addMessageContext <| ← Meta.inferType e
          depth    := depth
          status   := Status.lam
          thm      := "∀I" -- TODO use "→I" if it's purely implications?
          deps     := rdeps.reverse
          useAsDep := true }
      return (entry, entries)
  | .app .. => do
    trace[explode] ".app"

    -- We want to represent entire applications as a single line in the table
    let fn := e.getAppFn
    let args := e.getAppArgs

    -- If the function is a `const`, then it's not local so we do not need an
    -- entry in the table for it. We store the theorem name in the `thm` field
    -- below, giving access to the theorem's type on hover in the UI.
    -- Whether to include the entry could be controlled by a configuration option.
    let (fnEntry?, entries) ←
      if fn.isConst then
        pure (none, entries)
      else
        explodeCore fn depth entries
    let deps := if fn.isConst then [] else consDep fnEntry? []

    let mut entries' := entries
    let mut rdeps := []
    for arg in args do
      let (appEntry?, entries'') ← explodeCore arg depth entries'
      entries' := entries''
      rdeps := consDep appEntry? rdeps
    let deps := deps ++ rdeps.reverse

    let (entry, entries) := entries'.add e
      { type     := ← addMessageContext <| ← Meta.inferType e
        depth    := depth
        status   := Status.reg
        thm      := ← addMessageContext <| if fn.isConst then MessageData.ofConst fn else "∀E"
        deps     := deps
        useAsDep := true }
    return (entry, entries)
  | .letE varName varType val body _ => do
    trace[explode] ".letE"
    let varType := varType.cleanupAnnotations
    Meta.withLocalDeclD varName varType fun var => do
      let (valEntry?, entries) ← explodeCore val depth entries
      -- Add a synonym so that the substituted fvars refer to `valEntry?`
      let entries := valEntry?.map (entries.addSynonym var) |>.getD entries
      explodeCore (body.instantiate1 var) depth entries
  | _ => do
    -- Right now all of these are caught by this case case:
    --   Expr.lit, Expr.forallE, Expr.const, Expr.sort, Expr.mvar, Expr.fvar, Expr.bvar
    --   (Note: Expr.mdata is stripped by cleanupAnnotations)
    -- Might be good to handle them individually.
    trace[explode] ".{e.ctorName} (default handler)"
    let (entry, entries) := entries.add e
      { type     := ← addMessageContext <| ← Meta.inferType e
        depth    := depth
        status   := Status.reg
        thm      := ← addMessageContext e
        deps     := []
        useAsDep := ← select e }
    return (entry, entries)
where
  /-- Prepend the `line` of the `Entry` to `deps` if it's not `none`, but if the entry isn't marked
  with `useAsDep` then it's not added to the list at all. -/
  consDep (entry? : Option Entry) (deps : List (Option Nat)) : List (Option Nat) :=
    if let some entry := entry? then
      if includeAllDeps || entry.useAsDep then entry.line! :: deps else deps
    else
      deps

/-- Main definition behind `#explode` command. -/
def explode (e : Expr) (filterProofs : Bool := true) : MetaM Entries := do
  let filter (e : Expr) : MetaM Bool :=
    if filterProofs then Meta.isProof e else return true
  let (_, entries) ← explodeCore (start := true) filter false e 0 default
  return entries

open Elab in
/--
`#explode expr` displays a proof term in a line-by-line format somewhat akin to a Fitch-style
proof or the Metamath proof style.

For example, exploding the following theorem:

```lean
#explode iff_of_true
```

produces:

```lean
iff_of_true : ∀ {a b : Prop}, a → b → (a ↔ b)

0│         │ a         ├ Prop
1│         │ b         ├ Prop
2│         │ ha        ├ a
3│         │ hb        ├ b
4│         │ x✝        │ ┌ a
5│4,3      │ ∀I        │ a → b
6│         │ x✝        │ ┌ b
7│6,2      │ ∀I        │ b → a
8│5,7      │ Iff.intro │ a ↔ b
9│0,1,2,3,8│ ∀I        │ ∀ {a b : Prop}, a → b → (a ↔ b)
```

## Overview

The `#explode` command takes the body of the theorem and decomposes it into its parts,
displaying each expression constructor one at a time. The constructor is indicated
in some way in column 3, and its dependencies are recorded in column 2.

These are the main constructor types:

  - Lambda expressions (`Expr.lam`). The expression `fun (h : p) => s` is displayed as
    ```lean
     0│    │ h   │ ┌ p
     1│**  │ **  │ │ q
     2│1,2 │ ∀I  │ ∀ (h : p), q
    ```
    with `**` a wildcard, and there can be intervening steps between 0 and 1.
    Nested lambda expressions can be merged, and `∀I` can depend on a whole list of arguments.

  - Applications (`Expr.app`). The expression `f a b c` is displayed as
     ```lean
     0│**      │ f  │ A → B → C → D
     1│**      │ a  │ A
     2│**      │ b  │ B
     3│**      │ c  │ C
     1│0,1,2,3 │ ∀E │ D
     ```
     There can be intervening steps between each of these.
     As a special case, if `f` is a constant it can be omitted and the display instead looks like
     ```lean
     0│**    │ a │ A
     1│**    │ b │ B
     2│**    │ c │ C
     3│1,2,3 │ f │ D
     ```

  - Let expressions (`Expr.letE`) do not display in any special way, but they do
    ensure that in `let x := v; b` that `v` is processed first and then `b`, rather
    than first doing zeta reduction. This keeps lambda merging and application merging
    from making proofs with `let` confusing to interpret.

  - Everything else (constants, fvars, etc.) display `x : X` as
    ```lean
    0│  │ x │ X
    ```

## In more detail

The output of `#explode` is a Fitch-style proof in a four-column diagram modeled after Metamath
proof displays like [this](http://us.metamath.org/mpeuni/ru.html). The headers of the columns are
"Step", "Hyp", "Ref", "Type" (or "Expression" in the case of Metamath):
* **Step**: An increasing sequence of numbers for each row in the proof, used in the Hyp fields.
* **Hyp**: The direct children of the current step. These are step numbers for the subexpressions
  for this step's expression. For theorem applications, it's the theorem arguments, and for
  foralls it is all the bound variables and the conclusion.
* **Ref**: The name of the theorem being applied. This is well-defined in Metamath, but in Lean
  there are some special steps that may have long names because the structure of proof terms doesn't
  exactly match this mold.
  * If the theorem is `foo (x y : Z) : A x -> B y -> C x y`:
    * the Ref field will contain `foo`,
    * `x` and `y` will be suppressed, because term construction is not interesting, and
    * the Hyp field will reference steps proving `A x` and `B y`. This corresponds to a proof term
      like `@foo x y pA pB` where `pA` and `pB` are subproofs.
    * In the Hyp column, suppressed terms are omitted, including terms that ought to be
      suppressed but are not (in particular lambda arguments).
      TODO: implement a configuration option to enable representing suppressed terms using
      an `_` rather than a step number.
  * If the head of the proof term is a local constant or lambda, then in this case the Ref will
    say `∀E` for forall-elimination. This happens when you have for example `h : A -> B` and
    `ha : A` and prove `b` by `h ha`; we reinterpret this as if it said `∀E h ha` where `∀E` is
    (n-ary) modus ponens.
  * If the proof term is a lambda, we will also use `∀I` for forall-introduction, referencing the
    body of the lambda. The indentation level will increase, and a bracket will surround the proof
    of the body of the lambda, starting at a proof step labeled with the name of the lambda variable
    and its type, and ending with the `∀I` step. Metamath doesn't have steps like this, but the
    style is based on Fitch proofs in first-order logic.
* **Type**: This contains the type of the proof term, the theorem being proven at the current step.

Also, it is common for a Lean theorem to begin with a sequence of lambdas introducing local
constants of the theorem. In order to minimize the indentation level, the `∀I` steps at the end of
the proof will be introduced in a group and the indentation will stay fixed. (The indentation
brackets are only needed in order to delimit the scope of assumptions, and these assumptions
have global scope anyway so detailed tracking is not necessary.)
-/
elab "#explode " stx:term : command => withoutModifyingEnv <| Command.runTermElabM fun _ => do
  let (heading, e) ← try
    -- Adapted from `#check` implementation
    let theoremName : Name ← realizeGlobalConstNoOverloadWithInfo stx
    addCompletionInfo <| .id stx theoremName (danglingDot := false) {} none
    let decl ← getConstInfo theoremName
    let c : Expr := .const theoremName (decl.levelParams.map mkLevelParam)
    pure (m!"{MessageData.ofConst c} : {decl.type}", decl.value!)
  catch _ =>
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    pure (m!"{e} : {← Meta.inferType e}", e)
  unless e.isSyntheticSorry do
    let entries ← explode e
    let fitchTable : MessageData ← entriesToMessageData entries
    logInfo <|← addMessageContext m!"{heading}\n\n{fitchTable}\n"
