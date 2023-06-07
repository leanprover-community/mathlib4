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

open Lean Expr Meta

namespace Lean.Meta

/-- A "universe-polymorphic" expression. `{ expr, params } : ExprWithLevels` should be thought of
as a lambda `fun {params} => expr`, with the levels named by `params` being bound in `expr` and
regarded as implicit arguments. Displayed as `lfun params => expr` in `MessageData`. -/
structure ExprWithLevels where
  expr   : Expr
  params : Array Name
deriving Repr

instance : ToMessageData ExprWithLevels where
  toMessageData e := "lfun " ++ toMessageData e.params ++ " => " ++ toMessageData e.expr

/-- Given some `e : Expr`, create an `ExprWithLevels` with no level param arguments. -/
def _root_.Lean.Expr.toExprWithLevels (e : Expr) : ExprWithLevels := ⟨e,#[]⟩

namespace ExprWithLevels

/-- Apply `f` to the body of some `ExprWithLevels`. -/
def map : (e : ExprWithLevels) → (f : Expr → Expr) → ExprWithLevels
| ⟨expr, params⟩, f => ⟨f expr, params⟩

/-- Apply `f` to the body of some `ExprWithLevels`. -/
def mapM [Monad m] : (e : ExprWithLevels) → (f : Expr → m Expr) → m ExprWithLevels
| ⟨expr, params⟩, f => return ⟨← f expr, params⟩

/-- Checks if some `e : ExprWithLevels` represents a "constant" function in its bound level params.
I.e., that no level param in `e.expr` is contained in `e.params`. -/
def isConstantInLevelArgs (e : ExprWithLevels) : Bool :=
  ! (collectLevelParams {} e.expr |>.params.any e.params.contains)

/-- Removes parameter arguments which are unused in `(e : ExprWithLevels).expr`. -/
def removeConstantLevelArgs : ExprWithLevels → ExprWithLevels
| ⟨expr, params⟩ => ⟨expr, params.filter (collectLevelParams {} expr |>.params.contains)⟩

/-- Returns the body of an `ExprWithLevels` if `params` is empty. -/
def toExpr? (e : ExprWithLevels) : Option Expr := if e.params.isEmpty then some e.expr else none

/-- Returns the body of an `ExprWithLevels` if `params` is empty or if `ExprWithLevels` represents
a constant function with respect to `params`. -/
def toExpr'? (e : ExprWithLevels) : Option Expr :=
  if e.params.isEmpty || e.isConstantInLevelArgs then some e.expr else none

/-- A low-level "environment" used to associate "variables" (parameter names) to level
metavariables. Used when "telescoping" an `ExprWithLevels`.

We maintain the following assumptions:

* All elements of `levels` are level metavariables.
* `env.params.size == env.levels.size`; this lets us avoid extra zipping and unzipping compared to
  using an `Array (Name × Level)`. -/
structure Environment where
  params : Array Name
  levels : Array Level
deriving Repr

instance : EmptyCollection Environment := ⟨⟨#[],#[]⟩⟩

instance : ToMessageData Environment where
  toMessageData env :=
    let a := env.params.zipWith env.levels fun p l => toMessageData p ++ " ↤ " ++ toMessageData l
    MessageData.ofArray a

