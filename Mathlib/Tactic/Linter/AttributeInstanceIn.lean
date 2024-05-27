/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
# Linter for `attribute instance in` declarations

The syntax `attribute [instance] instName in` can be used to accidentally create a global instance.
This is **not** obvious from reading the code, and in fact happened twice during the port,
hence, we lint against it.

*Example*: before this was discovered, `Mathlib/Topology/Category/TopCat/Basic.lean`
contained the following code:
```
attribute [instance] ConcreteCategory.instFunLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f
```
Despite the `in`, this makes `ConcreteCategory.instFunLike` a global instance.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- Lint on any occurrence `attribute [instance] name in` (possibly with priority or scoped):
these are a footgun, as they define *global* instances (despite the `in`). -/
register_option linter.attributeInstanceIn : Bool := {
  defValue := true
  descr := "enable the attributeInstanceIn linter"
}

namespace attributeInstanceLinter

/-- Gets the value of the `linter.attributeInstanceIn` option. -/
def getLinterAttributeInstanceIn (o : Options) : Bool :=
  Linter.getLinterValue linter.attributeInstanceIn o

/-- Whether a syntax element is adding an `instance` attribute without a `local` modifier. -/
def is_attribute_instance_in (stx : Syntax) : Bool :=
  match stx with
  | `(command|attribute [instance] $_decl:ident in $_) => true
  | `(command|attribute [instance $_priority] $_decl:ident in $_) => true
  | _ => false

/--
`getAttrInstance cmd` assumes that `cmd` represents a `attribute [...] id in ...` command.
If this is the case, then it returns `(id, #[non-local nor scoped attributes])`.
Otherwise, it returns `default`.
-/
def getAttrInstance : Syntax → Syntax × Array Syntax
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.map (·.raw)
    let xs := xs.filter fun a => match a with
      | .node _ ``Lean.Parser.Command.eraseAttr _ => false
      | .node _ ``Lean.Parser.Term.attrInstance #[
        .node _ ``Lean.Parser.Term.attrKind #[
          .node _ _ #[.node _ scopedOrLocal _]], _attr] =>
        ! scopedOrLocal ∈ [``Lean.Parser.Term.scoped, ``Lean.Parser.Term.local]
      | _ => true
    (id, xs)
  | _ => default

/-- The `attributeInstanceLinter` linter flags any occurrence of `attribute [instance] name in`,
including scoped or with instance priority: despite the `in`, these define *global* instances,
which can be rather misleading.
Instead, remove the `in` or make this a `local instance` instead.
-/
def attributeInstanceIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterAttributeInstanceIn (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  if let some stx := stx.find? fun s => (getAttrInstance s).2.isEmpty then
    let (id, nonScopedNorLocal) := getAttrInstance stx
    let _ ← nonScopedNorLocal.mapM fun attr =>
    Linter.logLint linter.attributeInstanceIn attr m!
    "Despite the `in`, the attribute '{attr}' added globally to '{id}'\n\
      please remove the `in` or make this a `local instance` instead"

initialize addLinter attributeInstanceIn

end attributeInstanceLinter

end Mathlib.Linter
