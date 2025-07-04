/-
Copyright (c) 2025 Henrik Böving, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Yaël Dillies, Kyle Miller
-/
import Mathlib.Init
import Mathlib.Lean.Expr.Basic

/-!
# Tracking uses of `sorry`

This file provides a `#track_sorry` command to help find out why a given declaration is not
sorry-free. `#track_sorry foo` returns a non-sorry-free declaration `bar` which `foo` depends on,
if such `bar` exists.

## TODO

* Better handle the case where `foo` itself uses `sorry`: Currently, `#track_sorry foo` would return
  "`foo` depends on `foo` which isn't sorry-free".
* Generalise to other axioms/constants. This is easy, except for the fact that we need to find a
  nice syntax/name for the command.
* Move to ImportGraph?
-/

open Lean Meta Elab Command

namespace PrintSorries

/-- Type of intermediate computation of sorry-tracking. -/
structure State where
  /-- The set of already visited declarations. -/
  visited : NameSet := {}
  /-- The uses of `sorry` that were found. -/
  sorryMsgs : Array MessageData := #[]

/-- Collect all uses of `sorry` inside `c`. -/
partial def collect (c : Name) : StateT State MetaM Unit := do
  let collectExpr (e : Expr) : StateT State MetaM Unit := do
    e.getUsedConstants.forM collect
    if e.hasSorry then
      let seenSorriesRef : IO.Ref (Std.HashSet Expr) ← IO.mkRef {}
      discard <| Meta.transform (skipConstInApp := true) e (post := fun e => do
        if let some _ := isLabeledSorry? e then
          let e' := e.getBoundedAppFn (e.getAppNumArgs - 3)
          let seenSorries ← seenSorriesRef.get
          if !seenSorries.contains e' then
            seenSorriesRef.set (seenSorries.insert e')
            let mut msg := m!"{.ofConstName c} has {e'}"
            if e'.isSyntheticSorry then
              msg := msg ++ " (from error)"
            modify fun s => { s with sorryMsgs := s.sorryMsgs.push msg }
        else if e.isSorry then
          let e' := e.getBoundedAppFn (e.getAppNumArgs - 2)
          let seenSorries ← seenSorriesRef.get
          if !seenSorries.contains e' then
            seenSorriesRef.set (seenSorries.insert e')
            let mut msg := m!"{.ofConstName c} has sorryAx" -- no point in allowing hover
            if e'.isSyntheticSorry then
              msg := msg ++ " (from error)"
            modify fun s => { s with sorryMsgs := s.sorryMsgs.push msg }
        return .continue)
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

/-- Print all uses of `sorry` inside a list of declarations.
Each displayed sorry supports "go to definition". -/
def collectSorries (constNames : Array Name) : MetaM (Array MessageData) := do
  let (_, s) ← (constNames.forM collect).run {}
  pure s.sorryMsgs

/--
- `#print sorries` prints all sorries that the current module depends on
- `#print sorries id1 id2 ... idn` prints all sorries that the provided declarations depend on.

Each displayed sorry supports "go to definition".
-/
syntax "#print " &"sorries" (ppSpace ident)* : command

elab_rules : command
  | `(#print%$tk sorries $idents*) => withRef tk do
    let mut names ← liftCoreM <| idents.flatMapM fun id =>
      return (← realizeGlobalConstWithInfos id).toArray
    if names.isEmpty then
      names ← (← getEnv).checked.get.constants.map₂.foldlM (init := {}) fun acc name _ =>
        return if ← name.isBlackListed then acc else acc.push name
    let msgs ← liftTermElabM <| collectSorries names
    if msgs.isEmpty then
      logInfo m!"Declarations are sorry-free!"
    else
      logInfo <| MessageData.joinSep msgs.toList "\n"

end PrintSorries
