/-
Copyright (c) 2025 Henrik Böving, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Yaël Dillies
-/
import Mathlib.Init

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

open Lean Syntax Elab.Command

namespace TrackSorry

/-- Type of intermediate computation of axiom-tracking. -/
structure State where
  /-- The set of already visited declarations. -/
  visited : NameSet := {}
  /-- The uses of axioms that were found. -/
  axioms  : Array (Name × Name) := #[]

/-- Collect all uses of `c` inside `origin`. -/
partial def collect (origin c : Name) : ReaderT Environment (StateM State) Unit := do
  let collectExpr (origin : Name) (e : Expr) : ReaderT Environment (StateM State) Unit :=
    e.getUsedConstants.forM (collect origin)
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    match env.find? c with
    | some (.axiomInfo _)  => modify fun s => { s with axioms := s.axioms.push (origin, c) }
    | some (.defnInfo v)   => collectExpr c v.type *> collectExpr c v.value
    | some (.thmInfo v)    => collectExpr c v.type *> collectExpr c v.value
    | some (.opaqueInfo v) => collectExpr c v.type *> collectExpr c v.value
    | some (.quotInfo _)   => pure ()
    | some (.ctorInfo v)   => collectExpr c v.type
    | some (.recInfo v)    => collectExpr c v.type
    | some (.inductInfo v) => collectExpr c v.type *> v.ctors.forM (collect c)
    | none                 => pure ()

end TrackSorry

/-- `#track_sorry foo` returns a non-sorry-free declaration `bar` which `foo` depends on,
if such `bar` exists. -/
syntax (name := trackSorryStx) "#track_sorry" ident : command

elab_rules : command
  | `(#track_sorry $decl:ident) => do
    let env ← getEnv
    let declName ← liftCoreM <| realizeGlobalConstNoOverload decl
    let (_, s) := ((TrackSorry.collect declName declName).run env).run {}
    match s.axioms.find? (·.2 == `sorryAx) with
    | some (sorryDeclName, _) =>
      logInfoAt (← getRef)
        m!"{.ofConstName declName} depends on {.ofConstName sorryDeclName} which isn't sorry-free"
    | none =>
      logInfoAt (← getRef) m!"{.ofConstName declName} is sorry-free"
