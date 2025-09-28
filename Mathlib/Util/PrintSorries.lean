/-
Copyright (c) 2025 Henrik Böving, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Yaël Dillies, Kyle Miller
-/
import Mathlib.Lean.Expr.Basic

/-!
# Tracking uses of `sorry`

This file provides a `#print sorries` command to help find out why a given declaration is not
sorry-free. `#print sorries foo` returns a non-sorry-free declaration `bar` which `foo` depends on,
if such a `bar` exists.

The `#print sorries in CMD` combinator prints all sorries appearing in the declarations defined
by the given command.

## TODO

* Add configuration options. `#print sorries +positions -types` would print file/line/col
  information and not print the types.
* Make versions for other axioms/constants.
  The `#print sorries` command itself shouldn't be generalized, since `sorry` is a special concept,
  representing unfinished proofs, and it has special support for "go to definition", etc.
* Move to ImportGraph?
-/

open Lean Meta Elab Command

namespace Mathlib.PrintSorries

/-- Type of intermediate computation of sorry-tracking. -/
structure State where
  /-- The set of already visited declarations. -/
  visited : NameSet := {}
  /-- The set of `sorry` expressions that have been found.
  Note that unlabeled sorries will only be reported in the *first* declaration that uses them,
  even if a later definition independently has a direct use of `sorryAx`. -/
  sorries : Std.HashSet Expr := {}
  /-- The uses of `sorry` that were found. -/
  sorryMsgs : Array MessageData := #[]

/--
Collects all uses of `sorry` by the declaration `c`.
It finds all transitive uses as well.

This is a version of `Lean.CollectAxioms.collect` that keeps track of enough information to print
each use of `sorry`.
-/
partial def collect (c : Name) : StateT State MetaM Unit := do
  let collectExpr (e : Expr) : StateT State MetaM Unit := do
    /-
    We assume most declarations do not contain sorry.
    The `getUsedConstants` function is very efficient compared to `forEachExpr'`,
    since `forEachExpr'` needs to instantiate fvars.
    Visiting constants first also guarantees that we attribute sorries to the first
    declaration that included it. Recall that `sorry` might appear in the type of a theorem,
    which leads to the `sorry` appearing directly in any declarations that use it.
    This is one reason we need the `State.sorries` set as well.
    The other reason is that we match entire sorry applications,
    so `forEachExpr'`'s cache won't prevent over-reporting if `sorry` is a function.
    -/
    let consts := e.getUsedConstants
    consts.forM collect
    if consts.contains ``sorryAx then
      let visitSorry (e : Expr) : StateT State MetaM Unit := do
        unless (← get).sorries.contains e do
          let mut msg := m!"{.ofConstName c} has {e}"
          if e.isSyntheticSorry then
            msg := msg ++ " (from error)"
          try
            msg := msg ++ " of type" ++ indentExpr (← inferType e)
          catch _ => pure ()
          msg ← addMessageContext msg
          modify fun s =>
            { s with
              sorries := s.sorries.insert e
              sorryMsgs := s.sorryMsgs.push msg }
      Meta.forEachExpr' e fun e => do
        if e.isSorry then
          if let some _ := isLabeledSorry? e then
            visitSorry <| e.getBoundedAppFn (e.getAppNumArgs - 3)
          else
            visitSorry <| e.getBoundedAppFn (e.getAppNumArgs - 2)
          return false
        else
          -- Otherwise continue visiting subexpressions
          return true
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← getEnv
    match env.checked.get.find? c with
    | some (.axiomInfo v)  => collectExpr v.type
    | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
    | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
    | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (.quotInfo _)   => pure ()
    | some (.ctorInfo v)   => collectExpr v.type
    | some (.recInfo v)    => collectExpr v.type
    | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
    | none                 => pure ()

/--
Prints all uses of `sorry` inside a list of declarations.
Displayed sorries are hoverable and support "go to definition".
-/
def collectSorries (constNames : Array Name) : MetaM (Array MessageData) := do
  let (_, s) ← (constNames.forM collect).run {}
  pure s.sorryMsgs

/--
- `#print sorries` prints all sorries that the current module depends on.
- `#print sorries id1 id2 ... idn` prints all sorries that the provided declarations depend on.
- `#print sorries in CMD` prints all the sorries in declarations added by the command.

Displayed sorries are hoverable and support "go to definition".
-/
syntax (name := printSorriesStx) "#print " &"sorries" (ppSpace ident)* : command

/--
Collects sorries in the given constants and logs a message.
-/
def evalCollectSorries (names : Array Name) : CommandElabM Unit := do
  let msgs ← liftTermElabM <| collectSorries names
  if msgs.isEmpty then
    logInfo m!"Declarations are sorry-free!"
  else
    logInfo <| MessageData.joinSep msgs.toList "\n"

elab_rules : command
  | `(#print%$tk1 sorries%$tk2 $idents*) => do
    let mut names ← liftCoreM <| idents.flatMapM fun id =>
      return (← realizeGlobalConstWithInfos id).toArray
    if names.isEmpty then
      names ← (← getEnv).checked.get.constants.map₂.foldlM (init := #[]) fun acc name _ =>
        return if ← name.isBlackListed then acc else acc.push name
    withRef (mkNullNode #[tk1, tk2]) <| evalCollectSorries names

@[inherit_doc printSorriesStx]
syntax "#print " &"sorries" " in " command : command

elab_rules : command
  | `(#print%$tk1 sorries%$tk2 in $cmd:command) => do
    let oldEnv ← getEnv
    try
      elabCommand cmd
    finally
      let newEnv ← getEnv
      let names ← newEnv.checked.get.constants.map₂.foldlM (init := #[]) fun acc name _ => do
        if oldEnv.constants.map₂.contains name then
          return acc
        else if ← name.isBlackListed then
          return acc
        else
          return acc.push name
      withRef (mkNullNode #[tk1, tk2]) <| evalCollectSorries names

end Mathlib.PrintSorries
