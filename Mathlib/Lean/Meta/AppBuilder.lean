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

namespace Lean.Meta

/-- Like `mkAppN f xs`, but unifies the types of the arguments `xs` with the function `f`'s input
types, and therefore (unlike `mkAppN`) fails if any argument types are not defeq to the
corresponding input type. Note that, by design, this may assign metavariables at the current
MCtxDepth. -/
def mkAppNUnifying (f : Expr) (xs : Array Expr) (reducing := true): MetaM Expr := do
  mkAppNUnifyingArgs f (← inferType f) xs
where
  mkAppNUnifyingArgs (f fType : Expr) (xs : Array Expr) : MetaM Expr := withAppBuilderTrace f xs do
    let (args, _) ← xs.foldlM (init := (#[], 0, fType)) fun (args, j, type) x => do
      match type with
      | .forallE _ d b _ => do
        let d := d.instantiateRevRange j args.size args
        if (← isDefEq d (← inferType x)) then
          pure (args.push x, j, b)
        else
          throwAppTypeMismatch (mkAppN f args) x
      | type =>
        try
          guard reducing
          let type ← whnfD type
          guard type.isForall
          pure (args, args.size, type)
        catch _ =>
          tooManyExplicitArgsException `mkAppNUnifying f args.size xs
    instantiateMVars (mkAppN f args)


-/

