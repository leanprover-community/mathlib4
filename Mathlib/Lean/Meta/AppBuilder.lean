/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Thomas Murrills
-/
import Lean
import Std.Tactic.OpenPrivate
import Mathlib.Control.Basic
import Mathlib.Lean.Meta.ExprWithLevels

/-!

# Additions to Lean.Meta.AppBuilder

We provide variants of `mkAppM` and `mkAppN` for customized behavior. Namely:

* `mkApp*Unifying`(`'`): Checks that argument types are defeq to the corresponding input types, and
does not set a new MCtx depth

* `mkAppMUnifyingWithNewMVars`(`'`): Unifies at the current MCtx depth as above, and does not fail
if newly-created implicit argument mvars are unassigned, instead returning them along with the
`Expr`. Useful if we want to delay the assignment of these metavariables.

This includes specialized appbuilder functionality for `ExprWithLevels`.

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

namespace Lean.Meta

/-- Helper function for `mkAppNUnifying`. Separated out for use in case the type is known. -/
private def mkAppNUnifyingArgs (f fType : Expr) (xs : Array Expr) : MetaM Expr :=
  withAppBuilderTrace f xs do
    let (args, _) ← xs.foldlM (init := (#[], fType)) fun (args, type) x => do
      match type with
      | .forallE _ d b _ => do
        let d := d.instantiateRev args
        if (← isDefEq d (← inferType x)) then
          pure (args.push x, b)
        else
          throwAppTypeMismatch (mkAppN f args) x
      | _ => throwAppBuilderException `mkAppNUnifying m!"too many arguments provided to{
        indentExpr f}\narguments{indentD xs}"
    instantiateMVars (mkAppN f args)

/-- Like `mkAppN f xs`, but unifies the types of the arguments `xs` with the function `f`'s input
types, and therefore (unlike `mkAppN`) fails if any argument types are not defeq to the
corresponding input type. Note that, by design, this may assign metavariables at the current
MCtxDepth. -/
def mkAppNUnifying (f : Expr) (xs : Array Expr) : MetaM Expr := do
  mkAppNUnifyingArgs f (← inferType f) xs

/-- Like `mkAppMFinal`, but does not fail if unassigned metavariables are present. However, it does
fail if any *new* metavariables are present. -/
private def mkAppMFinalUnifying (methodName : Name) (f : Expr) (args : Array Expr)
    (mvars instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  unless ← (mvars.allM (·.isAssigned) <&&> instMVars.allM (·.isAssigned)) do
    throwAppBuilderException methodName ("result contains new metavariables" ++ indentExpr result)
  return result

/-- Like `mkAppMFinal`, but does not fail if unassigned metavariables are present. Returns any
unassigned new implicit mvars and instance MVars. -/
private def mkAppMFinalUnifyingWithNewMVars (_ : Name) (f : Expr) (args : Array Expr)
    (mvars instMVars : Array MVarId) : MetaM (Expr × Array MVarId × Array MVarId) := do
  instMVars.forM fun mvarId => tryM do
    unless ← mvarId.isAssigned do
      let mvarVal  ← synthInstance (← mvarId.getType)
      mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  return (result, ← mvars.filterM (notM ·.isAssigned), ← instMVars.filterM (notM ·.isAssigned))

/-- Nearly identical to `mkAppMArgs`, but passes a continuation for `mkAppMFinal` and keeps track
of any created implicit mvars. -/
private partial def mkAppMArgsUnifyingCont (n : Name) (f : Expr) (fType : Expr) (xs : Array Expr)
    (reducing : Bool) (k : Name → Expr → Array Expr → Array MVarId → Array MVarId → MetaM α)
    : MetaM α :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr)
      (mvars instMVars : Array MVarId) : MetaM α := do
    if i >= xs.size then
      k n f args mvars instMVars
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
        if reducing then
          let type ← whnfD type
          if type.isForall then
            loop type i args.size args mvars instMVars
          else
            throwAppBuilderException n m!"too many explicit arguments provided to{
              indentExpr f}\narguments{indentD xs}"
        else
          throwAppBuilderException n m!"too many explicit arguments provided to{
            indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[] #[]

/-- Like `mkAppM`, but allows metavariables to be unified during the construction of the
application. Fails if any metavariables for implicit arguments created during the course of
`mkAppMUnifying` are still unassigned; to return these mvars, use `mkAppMUnifyingWithNewMVars`. -/
def mkAppMUnifying (const : Name) (xs : Array Expr) (reducing := true)
    : MetaM Expr :=
  withAppBuilderTrace const xs do
    let (f, fType) ← mkFun const
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifying

/-- Like `mkAppM'`, but allows metavariables to be unified during the construction of the
application. Fails if any metavariables for implicit arguments created during the course of
`mkAppMUnifying'` are still unassigned; to return these mvars, use `mkAppMUnifyingWithNewMVars'`. -/
def mkAppMUnifying' (f : Expr) (xs : Array Expr) (reducing := true)
    : MetaM Expr :=
  withAppBuilderTrace f xs do
    mkAppMArgsUnifyingCont decl_name% f (← inferType f) xs reducing mkAppMFinalUnifying

local instance : ToMessageData (Expr × Array MVarId × Array MVarId) where
  toMessageData := fun (e, m₁, m₂) =>
    toMessageData e ++
      "\nimplicit mvars:\n" ++ toMessageData m₁ ++
      "\ninstance mvars:\n" ++ toMessageData m₂

/-- Like `mkAppNUnifying`, but returns `(e, implicitMVars, instMVars)` where `implicitMVars` and
`instMVars` are any newly-created metavariables for the implicit and instance arguments of `const`.
Useful in case we want to e.g. try assigning the `implicitMVars` with `isDefEq` afterwards, or if
we want to try synthesizing instance arguments later. -/
def mkAppMUnifyingWithNewMVars (const : Name) (xs : Array Expr) (reducing := true)
    : MetaM (Expr × Array MVarId × Array MVarId) :=
  withAppBuilderTrace' const xs do
    let (f, fType) ← mkFun const
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifyingWithNewMVars

/-- Like `mkAppNUnifyingWithNewMVars'`, but returns `(e, implicitMVars, instMVars)`. Useful in case
we want to e.g. try assigning the `implicitMVars` with `isDefEq` or if we want to try synthesizing
instance arguments later. -/
def mkAppMUnifyingWithNewMVars' (f : Expr) (xs : Array Expr) (reducing := true)
    : MetaM (Expr × Array MVarId × Array MVarId) :=
  withAppBuilderTrace' f xs do
    mkAppMArgsUnifyingCont decl_name% f (← inferType f) xs reducing mkAppMFinalUnifyingWithNewMVars

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

/-- Like `mkAppN (f : ExprWithLevels).expr xs`, but handles level arguments appropriately by
instantiating them with metavariables and then abstracting any that are not assigned. -/
def mkAppNWithLevels (f : ExprWithLevels) (xs : Array Expr) : MetaM ExprWithLevels :=
  withNewMCtxDepth do
    let (env, f) ← levelMetaTelescope f
    let e ← mkAppNUnifying f xs
    abstract env e

/-- Like `mkAppM'`, but handles "free" universe levels in `f` given by `params`. This converts
`params` in `f` and its type to level mvars `us`, constructs `f xs₁ xs₂ ... xsₙ`, then reverts any
`us` that were not assigned to their original universe params and returns the names of those params.
-/
def mkAppMWithLevels' (f : ExprWithLevels) (xs : Array Expr) (reducing := true)
    : MetaM ExprWithLevels :=
  withNewMCtxDepth do
    let (env, f) ← levelMetaTelescope f
    let fType ← inferType f
    let e ← withAppBuilderTrace f xs do
      mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifying
    abstract env e

/-- Like `mkAppMWithLevels'`, but unifies the types of the arguments, and thus may assign
metavariables, akin to `mkAppMUnifying'`. -/
def mkAppMWithLevelsUnifying' (f : ExprWithLevels) (xs : Array Expr) (reducing := true)
    : MetaM ExprWithLevels := do
  let (env, f) ← levelMetaTelescope f
  let fType ← inferType f
  let e ← withAppBuilderTrace f xs do
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifying
  abstract env e

/-- Like `mkAppMWithLevelsUnifying'`, but returns any new mvars created. -/
def mkAppMWithLevelsUnifyingWithNewMVars' (f : ExprWithLevels) (xs : Array Expr) (reducing := true)
    : MetaM (ExprWithLevels × Array MVarId × Array MVarId) := do
  let (env, f) ← levelMetaTelescope f
  let fType ← inferType f
  let (e, implicitMVars, instMVars) ← withAppBuilderTrace' f xs do
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifyingWithNewMVars
  return (← abstract env e, implicitMVars, instMVars)

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
