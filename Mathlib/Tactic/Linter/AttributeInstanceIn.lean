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

This seems to apply to all attributes.
```lean
theorem what : False := sorry

attribute [simp] what in
#guard true

-- the `simp` attribute persists
example : False := by simp  -- `simp` finds `what`

theorem who {x y : Nat} : x = y := sorry

attribute [ext] who in
#guard true

-- the `ext` attribute persists
example {x y : Nat} : x = y := by ext
```

For *removing* instances, the `in` works as expected.
```lean
/--
error: failed to synthesize
  Add Nat
-/
#guard_msgs in
attribute [-instance] instAddNat in
#synth Add Nat

-- the `instance` persists
/-- info: instAddNat -/
#guard_msgs in
#synth Add Nat

@[simp]
theorem what : False := sorry

/-- error: simp made no progress -/
#guard_msgs in
attribute [-simp] what in
example : False := by simp

-- the `simp` attribute persists
#guard_msgs in
example : False := by simp
```
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

/--
`getAttrInstance cmd` assumes that `cmd` represents a `attribute [...] id in ...` command.
If this is the case, then it returns `(id, #[non-local nor scoped attributes])`.
Otherwise, it returns `default`.
-/
def getAttrInstance? : Syntax → Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

/-- The `attributeInstanceLinter` linter flags any occurrence of `attribute [instance] name in`,
including scoped or with instance priority: despite the `in`, these define *global* instances,
which can be rather misleading.
Instead, remove the `in` or make this a `local instance`.
-/
def attributeInstanceIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterAttributeInstanceIn (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let .some (id, nonScopedNorLocal) := getAttrInstance? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.attributeInstanceIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local instance` instead"

initialize addLinter attributeInstanceIn

end attributeInstanceLinter

end Mathlib.Linter
