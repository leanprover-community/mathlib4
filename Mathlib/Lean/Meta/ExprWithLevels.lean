/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Mathlib.Lean.Meta.Basic

/-!

# ExprWithLevels

The functionality provided by this file is meant to emulate a "universe-polymorphic expression".
That is, we'd like to write something like `fun {u : Level} {v : Level} ... => body`, but Lean
doesn't allow this to work the way we'd like—`u`, `v`, etc. can't be used as universes in `body`.
Lean doesn't allow bound universe variables; instead, each level parameter ``u := .param `u`` only
functions as a free universe variable.

Instead, Lean only allows level parameters to be attached to constants, and level parameters for a
given constant `const` are stored in `← getConstInfo f`. The resulting `ConstantInfo` (which has a
field `.params`) effectively fulfills the role of "binding" the level params (i.e. free universe
variables) in `f` at the meta level.

An `ExprWithLevels` follows this pattern, and simply packages an array of level params (as `Name`s)
with an `Expr`. The provided API for handling an `e : ExprWithLevels` effectively treats `e` as a
lambda with body `e.expr` and implicit level arguments `e.params`. E.g., we can appropriately
replacing these with level mvars when constructing an application of such a lambda, then re-bind
the mvars that didn't get assigned.

-/

