/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Util.AddRelatedDecl

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.NonemptyAttr

/-- Given an expression assumed of type `α`, returns an expression for of type `Nonempty α`. -/
def toNonempty (e : Expr) : MetaM Expr := do
  mapForallTelescope
    (fun e' => do
      let e ← instantiateMVars e'
      let e2 ← mkAppM ``Nonempty.intro #[e]
      return e2) e

/-- The configuration options for the `nonempty` attribute. -/
structure Config where
  /-- If true, register the generated `Nonempty _` declaration as an instance. -/
  inst : Bool := true

/-- Function elaborating `Push.Config`. -/
declare_command_config_elab elabNonemptyConfig Config

/-- Syntax for optional instance priority argument in the `nonempty` attribute -/
syntax optPrio := atomic("(" &"priority" ":=" prio ")")?

/-- Syntax for optional instance name argument in the `nonempty` attribute -/
syntax optName := atomic("(" &"name" ":=" ident ")")?

--TODO: more doc
/-- The `nonempty` attribute. -/
syntax (name := nonempty) "nonempty" optPrio optName Parser.Tactic.optConfig : attr

initialize registerBuiltinAttribute {
  name := `nonempty
  descr := "Adds a declaration of type `Nonempty α` when tagging a declaration of type `α`"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| nonempty $[(priority := $n:num)]? $[(name := $q:ident)]? $c:optConfig) => do
    let prio : Option Nat := n.map (·.getNat)
    let name : Option Name := q.map (·.getId)
    let cfg ← liftCommandElabM <| elabNonemptyConfig c
    MetaM.run' do
    addRelatedInst src ref (prio := prio.getD (eval_prio default))
      (name? := name) (inst := cfg.inst)
      (kind := kind) (hoverInfo := true)
      fun value levels => do
        let newValue ← (toNonempty value)
        pure (newValue, levels)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic.NonemptyAttr

end
