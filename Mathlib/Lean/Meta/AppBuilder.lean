/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Thomas Murrills
-/
import Lean
import Std.Tactic.OpenPrivate
import Mathlib.Lean.Meta.ExprWithLevels

/-!

# Additions to Lean.Meta.AppBuilder

This includes specialized appbuilder functionality for `ExprWithLevels`.

-/

open Lean Meta

open private throwAppBuilderException withAppBuilderTrace from Lean.Meta.AppBuilder

namespace Lean.Meta

/-- Helper function for `mkAppNUnifyingTypes`. Separated out for use in case the type is known. -/
private def mkAppNUnifyingTypesArgs (f fType : Expr) (xs : Array Expr) : MetaM Expr :=
  withAppBuilderTrace f xs do
    let (args, _) ← xs.foldlM (init := (#[], fType)) fun (args, type) x => do
      match type with
      | .forallE _ d b _ => do
        let d := d.instantiateRev args
        if (← isDefEq d (← inferType x)) then
          pure (args.push x, b)
        else
          throwAppTypeMismatch (mkAppN f args) x
      | _ => throwAppBuilderException `mkAppNUnifyingTypes' m!"too many arguments provided to{
        indentExpr f}\narguments{indentD xs}"
    instantiateMVars (mkAppN f args)

/-- Like `mkAppN f xs`, but unifies the types of the arguments `xs` with the function `f`'s input
types. Note that, by design, this may assign metavariables. -/
def mkAppNUnifyingTypes (f : Expr) (xs : Array Expr) : MetaM Expr := do
  mkAppNUnifyingTypesArgs f (← inferType f) xs

