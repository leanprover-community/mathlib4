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
  if is_attribute_instance_in stx then
    Linter.logLint linter.attributeInstanceIn stx[0] m!
      "`attribute [instance] ... in` declarations are surprising:\n\
      they are **not** limited to the subsequent declaration, but define global instances\n\
      please remove the `in` or make this a `local instance` instead"

initialize addLinter attributeInstanceIn

end attributeInstanceLinter

end Mathlib.Linter
