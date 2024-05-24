/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
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
-- Porting note: cannot find a coercion to function otherwise
attribute [instance] ConcreteCategory.instFunLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f
```
Despite the in, this makes `ConcreteCategory.instFunLike` a global instance.
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
  | `(command|attribute [instance] $_decl:ident) => true
  | `(command|attribute [instance $_priority] $_decl:ident) => true
  | _ => false

def attributeInstanceIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterAttributeInstanceIn (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  match stx.findStack? (fun _ ↦ true) is_attribute_instance_in with
  | some ((head, 0)::chain) =>
    -- An instance attribute is always the first child of its parent syntax.
    if is_attribute_instance_in head then
      -- Whether we have an e.g. scoped instance, and whether it's a global instance of just
      -- "in" the next declaration (the case we're linting against) depends on the parent.

      -- Its parent determines whether we have a scoped instance, and whether it's "in".
      -- scoped instance, no in: parent is the instance declaration of positive index
      -- non-scoped, no in: parent is empty
      -- "in" attribute: something non-trivial of index 0
      match chain.get? 0 with
      -- This is the case we're interested in
      | some (_next, 0) => Linter.logLint linter.attributeInstanceIn head m!
      "careful: `attribute [instance] ... in` declarations are surprising:
      they are **not** limited to the subsequent declaration,
      but define global instances
      please remove the `in` or make this a `local instance` instead"
      -- This is e.g. a scoped instance, which we don't care about.
      | some (_next, _n) => return
      -- This is an instance attribute without "in": fully legitimate and not surprising.
      | none => return
  | _ => return

initialize addLinter attributeInstanceIn

end attributeInstanceLinter

end Mathlib.Linter
