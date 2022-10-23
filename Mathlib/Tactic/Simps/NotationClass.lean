/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import Std.Lean.NameMapAttribute
import Lean.Structure

/-!
# `@[notation_class]` attribute for `@[simps]`

We put this in a separate file so that we can already tag some declarations with this attribute
in the file where we declare `@[simps]`. For further documentation, see `Tactic.Simps.Basic`.
-/

/-- The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].

  Note: this does *not* work yet for heterogenous operations like `HAdd`.
-/
syntax (name := notation_class) "notation_class" : attr

open Lean

/- todo: should this be TagAttribute? Can we "initialize" TagAttribute with a certain cache? -/
/-- `@[notation_class]` attribute -/
initialize notationClassAttr : NameMapExtension Unit ←
  registerNameMapAttribute {
    name  := `notation_class
    descr := "An attribute specifying that this is a notation class. Used by @[simps]."
    add   := fun
    | nm, `(attr|notation_class) => do
      if (getStructureInfo? (← getEnv) nm).isNone then
        throwError "@[notation_class] attribute can only be added to classes."
    | _, stx => throwError "unexpected notation_class syntax {stx}" }
