/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Thomas Murrills
-/
import Lean
import Std.Tactic.OpenPrivate

/-!

# Additions to Lean.Meta.AppBuilder

We provide variants of `mkAppM` and `mkAppN` for customized behavior. Namely:

* `mkApp*Unifying`(`'`): Checks that argument types are defeq to the corresponding input types, and
does not set a new MCtx depth

* `mkAppMUnifyingWithNewMVars`(`'`): Unifies at the current MCtx depth as above, and does not fail
if newly-created implicit argument mvars are unassigned, instead returning them along with the
`Expr`. Useful if we want to delay the assignment of these metavariables.


-/

open Lean Meta

open private mkFun throwAppBuilderException withAppBuilderTrace from Lean.Meta.AppBuilder

/-- Like `withAppBuilderTrace`, but generalized to arbitrary return types. -/
private def withAppBuilderTrace' [ToMessageData α] [ToMessageData β] [ToMessageData γ]
    (f : α) (xs : β) (k : MetaM γ) : MetaM γ :=
  let emoji | .ok .. => checkEmoji | .error .. => crossEmoji
  withTraceNode `Meta.appBuilder (return m!"{emoji ·} f: {f}, xs: {xs}") do
    try
      let res ← k
      trace[Meta.appBuilder.result] "{res}"
      pure res
    catch ex =>
      trace[Meta.appBuilder.error] ex.toMessageData
      throw ex

private def tooManyExplicitArgsException (n : Name) (f : Expr) (used : Nat) (provided : Array Expr)
    : MetaM α :=
  throwAppBuilderException n m!"too many explicit arguments provided to{indentExpr f}\nexpected {
    used}, got {provided.size}.\nused:{indentD provided[0:used]}\nunused:{indentD provided[used:]
    }"


-/

