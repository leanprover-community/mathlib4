/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
# The `attribute instance in linter`

TODO write doc comment: see zulip

During the port we accidentally made ConcreteCategory.instFunLike a global instance in Mathlib/Topology/Category/TopCat/Basic.lean:
-- Porting note: cannot find a coercion to function otherwise
attribute [instance] ConcreteCategory.instFunLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f

Despite the in, this makes it a global instance (we desperately need a linter for this!!!).

-/

open Lean Elab Command

namespace Mathlib.Linter

/-- Lint on any `attribute [instance ...] ... in`:
these are a footgun, as they define *global* instances (not local ones). -/
register_option linter.attributeInstanceIn : Bool := {
  defValue := true
  descr := "enable the attributeInstanceIn linter"
}

namespace attributeInstanceLinter

/-- Gets the value of the `linter.attributeInstanceIn` option. -/
def getLinterAttributeInstanceIn (o : Options) : Bool :=
  Linter.getLinterValue linter.attributeInstanceIn o

/-- Whether a syntax element is an `attribute [instance] instancename in` element.
Optionally, with instance priority or other bells and whistles. -/
def is_attribute_instance_in (stx : Syntax) : Bool :=
  match stx with
  | `(attribute [instance] $name in) => true
  | => false

def attributeInstanceIn : Linter where run := withSetOptionIn fun stx => do
  if getLinterAttributeInstanceIn (← getOptions) || (← MonadState.get).messages.hasErrors then
    return


initialize addLinter attributeInstanceIn

end instanceLinter

end Mathlib.Linter
