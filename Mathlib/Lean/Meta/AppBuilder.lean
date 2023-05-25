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

namespace ExprWithLevels

/-- Given a `const : Name`, produce `(f, fType, env)`, where

* `f` is the expression representing `const`
* `fType` is the type of `f`
* `env` is the assignment of the level params of `const` to new level metavariables.

The level params in `f` and `fType` are instantiated with these new level metavariables.
-/
def mkFunWithLevels (const : Name) : MetaM (Expr × Expr × Environment) := do
  let cinfo ← getConstInfo const
  let paramList := cinfo.levelParams
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := Expr.const const us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType, ⟨paramList.toArray, us.toArray⟩)

/-- Like `mkAppMFinal`, but does not fail if unassigned metavariables are present. Whether it fails if any newly-created metavariables are still unassigned is controlled by `allowNewMVars`. -/
private def mkAppMFinalAllowingMVars (methodName : Name) (f : Expr) (args : Array Expr)
    (mvars instMVars : Array MVarId) (allowNewMVars : Bool) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  unless allowNewMVars do
    unless ← (mvars.allM (·.isAssigned) <&&> instMVars.allM (·.isAssigned)) do
      throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  return result

/-- Nearly identical to `mkAppMArgs`, but uses `mkAppMFinalAllowingMVars`, and passes it any mvarIds
it creates. -/
private partial def mkAppMArgsAllowingMVars (f : Expr) (fType : Expr) (xs : Array Expr)
    (allowNewMVars : Bool) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr)
      (mvars instMVars : Array MVarId) : MetaM Expr := do
    if i >= xs.size then
      mkAppMFinalAllowingMVars `mkAppM f args mvars instMVars allowNewMVars
    else match type with
      | Expr.forallE n d b bi =>
        let d  := d.instantiateRevRange j args.size args
        match bi with
        | BinderInfo.implicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) (mvars.push mvar.mvarId!) instMVars
        | BinderInfo.strictImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) (mvars.push mvar.mvarId!) instMVars
        | BinderInfo.instImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          loop b i j (args.push mvar) mvars (instMVars.push mvar.mvarId!)
        | _ =>
          let x := xs[i]!
          let xType ← inferType x
          if (← isDefEq d xType) then
            loop b (i+1) j (args.push x) mvars instMVars
          else
            throwAppTypeMismatch (mkAppN f args) x
      | type =>
        let type := type.instantiateRevRange j args.size args
        let type ← whnfD type
        if type.isForall then
          loop type i args.size args mvars instMVars
        else
          throwAppBuilderException `mkAppM m!"too many explicit arguments provided to{
            indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[] #[]

/-- Like `mkAppN (f : ExprWithLevels).expr xs`, but handles level arguments appropriately by
instantiating them with metavariables and then abstracting any that are not assigned. -/
def mkAppNWithLevels (f : ExprWithLevels) (xs : Array Expr) : MetaM ExprWithLevels :=
  withNewMCtxDepth do
    let (env, f) ← levelMetaTelescope f
    let e ← mkAppNUnifyingTypes f xs
    abstract env e

/-- Like `mkAppM'`, but handles "free" universe levels in `f` given by `params`. This converts
`params` in `f` and its type to level mvars `us`, constructs `f xs₁ xs₂ ... xsₙ`, then reverts any
`us` that were not assigned to their original universe params and returns the names of those params.
-/
def mkAppMWithLevels' (f : ExprWithLevels) (xs : Array Expr) : MetaM ExprWithLevels :=
  withNewMCtxDepth do
    let (env, f) ← levelMetaTelescope f
    let fType ← inferType f
    let e ← withAppBuilderTrace f xs do mkAppMArgsAllowingMVars f fType xs false
    abstract env e

section Combinators

variable [MonadControlT MetaM m] [Monad m]

@[inline] private def mapWithConstLevelsMetaM
    (f : forall {α}, ((β → γ → MetaM δ) → β → γ → γ → MetaM α) → MetaM α) {α}
    (k : (β → γ → m δ) → β → γ → γ → m α) : m α :=
  controlAt MetaM fun runInBase => f fun a b' c' d' =>
    runInBase <| k (fun b c => liftWith fun _ => a b c) b' c' d'

/-- Evaluates `k := fun abstract env f fType => ...` on the `Expr` `f` referred to by `const` and
its type `fType`, with the const's level params replaced with metavariables according to `env`.

The arguments `abstract` and `env` of `k` can be used within the body of `k` to "re-bind" any of
these level metavariables that appear in some `e` to obtain an `ExprWithLevels`, e.g.
`abstract env e`. -/
def withConstLevels (const : Name)
    (k : (Environment → Expr → m ExprWithLevels) → Environment → Expr → Expr → m α)
    (abstract := abstract (m := MetaM)) : m α :=
  mapWithConstLevelsMetaM (fun k => do
    let (f, fType, env) ← mkFunWithLevels const
    k abstract env f fType) k

/-- Evaluates `k := fun env f fType => ...` on the `Expr` `f` referred to by `const` and
its type `fType`, with the const's level params replaced with metavariables according to `env`. The
remaining unassigned level metavariables in the `Expr` produced by `k` will be abstracted out into
an `ExprWithLevels` by `abstract`. -/
def withConstLevelsExpr (const : Name) (k : Environment → Expr → Expr → m Expr)
    (abstract := abstract (m := MetaM)) : m ExprWithLevels :=
  withConstLevels const (abstract := abstract) fun abstract env f fType => do
    abstract env (← k env f fType)

/-- Evaluates `k := fun env f fType => ...` on the `Expr` `f` referred to by `const` and
its type `fType`, with the const's level params replaced with metavariables according to `env`. The
remaining unassigned level metavariables in the `Expr` produced in the first component of `k`'s
output will be abstracted out into an `ExprWithLevels` by `abstract`. -/
def withConstLevelsExpr' (const : Name) (k : Environment → Expr → Expr → m (Expr × α))
    (abstract := abstract (m := MetaM)) : m (ExprWithLevels × α) :=
  withConstLevels const (abstract := abstract) fun abstract env f fType => do
    let (e, a) ← k env f fType
    return (← abstract env e, a)

end Combinators
