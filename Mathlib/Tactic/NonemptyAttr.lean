/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public meta import Mathlib.Util.AddRelatedDecl

/-! The `nonempty` attribute

When adding the `[nonempty]` attribute to a definition of type `α`,
a declaration of type `Nonempty α` is automatically generated and is
registered as an instance.

This can be used to make available to the typeclass system facts that
derive from the mere existence of an object of type `α` without making
`α` a class.

For instance, given a functor `F : C ⥤ D` between categories,
the data of some fully faithful structure `ffStruct : F.FullyFaithful` on `F`
allows one to derive `F.Full` and `F.Faithful`. However, this fact
cannot be directly made available to typeclass synthesis, as the
`FullyFaithful` structure is not a class (to avoid potential diamonds with
such data-carrying classes).
To avoid following every `FullyFaithful` declaration by two instance declarations,
one can tag such declaration with `@[nonempty]` so that, when combined with
instances of the form
```
instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [Nonempty F.FullyFaithful] :
    F.Full := …

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [Nonempty F.FullyFaithful] :
    F.Faithful := …
```
instances can be synthesized for `F.Full` and `F.Faithful`.

- `@[nonempty (name := foo)]` names the resulting instance `foo`.
- `@[nonempty (priority := 123)]` gives the resulting instance a priority of `123`.
- `@[nonempty -inst]` does not register the instance.
- If the attribute is made local or scoped, the same modifier is applied to the resulting instance.
-/

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

/-- Function elaborating `NonemptyAttr.Config`. -/
declare_command_config_elab elabNonemptyConfig Config

/-- Syntax for optional instance priority argument in the `nonempty` attribute -/
syntax optPrio := atomic("(" &"priority" ":=" prio ")")?

/-- Syntax for optional instance name argument in the `nonempty` attribute -/
syntax optName := atomic("(" &"name" ":=" ident ")")?

/-- When adding the `[nonempty]` attribute to a definition of type `α`,
a declaration of type `Nonempty α` is automatically generated and is
registered as an instance.

This can be used to make available to the typeclass system facts that
derive from the mere existence of an object of type `α` without making
`α` a class.

For instance, given a functor `F : C ⥤ D` between categories,
the data of some fully faithful structure `ffStruct : F.FullyFaithful` on `F`
allows one to obtain `F.Full` and `F.Faithful`. However, this fact
cannot be directly made available to typeclass synthesis, as the
`FullyFaithful` structure is not a class (to avoid potential diamonds with
such data-carrying classes).
To avoid following every single `FullyFaithful` declaration by two instance declarations,
one can tag such declarations with `@[nonempty]` so that, when combined with
instances of the form
```
instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [Nonempty F.FullyFaithful] :
    F.Full := …

instance {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [Nonempty F.FullyFaithful] :
    F.Faithful := …
```
instances can be synthesized for `F.Full` and `F.Faithful`.

- `@[nonempty (name := foo)]` names the resulting instance `foo`.
- `@[nonempty (priority := 123)]` gives the resulting instance a priority of `123`.
- `@[nonempty -inst]` does not register the instance.
- If the attribute is made local or scoped, the same modifier is applied to the resulting instance.
-/
syntax (name := nonempty) "nonempty" optPrio optName Parser.Tactic.optConfig : attr

initialize registerBuiltinAttribute {
  name := `nonempty
  descr := "Add an instance of type `Nonempty α` when tagging a declaration of type `α`"
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
