/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Thomas Murrills
-/
import Lean
import Std.Tactic.OpenPrivate
import Mathlib.Control.Basic
import Mathlib.Tactic.Alias

/-!

# Additions to Lean.Meta.AppBuilder

We provide variants of `mkAppM` and `mkAppN` for customized behavior. Namely:

* `mkApp*Unifying`(`'`): Checks that argument types are defeq to the corresponding input types, and
does not set a new MCtx depth

* `mkAppMUnifyingWithNewMVars`(`'`): Unifies at the current MCtx depth as above, and does not fail
if newly-created implicit argument mvars are unassigned, instead returning them along with the
`Expr`. Useful if we want to delay the assignment of these metavariables.

# Notes

Note that we frequently use `decl_name%` in non-dynamic way simply to avoid mistakes when passing
a function's name to itself.
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

/-- An informative exception for providing too many explicit arguments. -/
private def tooManyExplicitArgsException (n : Name) (f remainingType : Expr) (used : Nat)
    (provided : Array Expr) : MetaM α :=
  throwAppBuilderException n m!"too many explicit arguments provided to{indentExpr f}\nExpected {
    remainingType} to be a function type. Used {used} arguments, got {provided.size}.\nused:{
    indentD provided[0:used]}\nunused:{indentD provided[used:]}"

namespace Lean.Meta

/-- Like `mkAppN f xs`, but unifies the types of the arguments `xs` with the function `f`'s input
types, and therefore (unlike `mkAppN`) fails if any argument types are not defeq to the
corresponding input type.

Note that, by design, this may assign metavariables at the current MCtxDepth. -/
def mkAppNUnifying (f : Expr) (xs : Array Expr) (reducing := true) : MetaM Expr := do
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
          tooManyExplicitArgsException `mkAppNUnifying f type args.size xs
    instantiateMVars (mkAppN f args)

/-- Like `mkAppMFinal`, but does not fail if unassigned metavariables are present. However, it does
fail if any *new* metavariables are present. -/
private def mkAppMFinalUnifying (methodName : Name) (f : Expr) (args : Array Expr)
    (mvars instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarVal ← synthInstance (← mvarId.getType)
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
      mvarId.assign (← synthInstance (← mvarId.getType))
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
            tooManyExplicitArgsException n f type i xs
        else
          tooManyExplicitArgsException n f type i xs
  loop fType 0 0 #[] #[] #[]

/-- Like `mkAppM`, but allows metavariables at the current MCtxDepth to be unified during the
construction of the application. Fails if any metavariables for implicit arguments created during
the course of `mkAppMUnifying` are still unassigned; to return these mvars instead of failing, use
`mkAppMUnifyingWithNewMVars`.

If `reducing` is `true` (the default), reduces the argument types of `const` at default
transparency. -/
def mkAppMUnifying (const : Name) (xs : Array Expr) (reducing := true) : MetaM Expr :=
  withAppBuilderTrace const xs do
    let (f, fType) ← mkFun const
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifying

/-- Like `mkAppM'`, but allows metavariables to be unified during the construction of the
application. Fails if any metavariables for implicit arguments created during the course of
`mkAppMUnifying'` are still unassigned; to return these mvars instead of failing, use
`mkAppMUnifyingWithNewMVars'`.

If `reducing` is `true` (the default), reduces the argument types of `f` at default transparency. -/
def mkAppMUnifying' (f : Expr) (xs : Array Expr) (reducing := true) : MetaM Expr :=
  withAppBuilderTrace f xs do
    mkAppMArgsUnifyingCont decl_name% f (← inferType f) xs reducing mkAppMFinalUnifying

local instance : ToMessageData (Expr × Array MVarId × Array MVarId) where
  toMessageData := fun (e, m₁, m₂) =>
    toMessageData e ++
      "\nunassigned implicit mvars:\n" ++ toMessageData m₁ ++
      "\nunassigned instance mvars:\n" ++ toMessageData m₂

/-- Like `mkAppNUnifying`, but returns `(e, implicitMVars, instMVars)` where `implicitMVars` and
`instMVars` are any newly-created unassigned metavariables for the implicit and instance arguments
of `const`. Useful in case we want to e.g. try assigning the `implicitMVars` or synthesizing the
instance arguments later.

If `reducing` is `true` (the default), reduces the argument types of `const` at default
transparency. -/
def mkAppMUnifyingWithNewMVars (const : Name) (xs : Array Expr) (reducing := true)
    : MetaM (Expr × Array MVarId × Array MVarId) :=
  withAppBuilderTrace' const xs do
    let (f, fType) ← mkFun const
    mkAppMArgsUnifyingCont decl_name% f fType xs reducing mkAppMFinalUnifyingWithNewMVars

/-- Like `mkAppMUnifying'`, but returns `(e, implicitMVars, instMVars)` where `implicitMVars` and
`instMVars` are any newly-created unassigned metavariables for the implicit and instance arguments
of `const`. Useful in case we want to e.g. try assigning the `implicitMVars` or synthesizing the
instance arguments later.

If `reducing` is `true` (the default), reduces the argument types of `f` at default transparency. -/
def mkAppMUnifyingWithNewMVars' (f : Expr) (xs : Array Expr) (reducing := true)
    : MetaM (Expr × Array MVarId × Array MVarId) :=
  withAppBuilderTrace' f xs do
    mkAppMArgsUnifyingCont decl_name% f (← inferType f) xs reducing mkAppMFinalUnifyingWithNewMVars

/-- `mkFun constName` returns `(f, fType)` with fresh level mvars, where `f` =
`.const constName us`. -/
alias mkFun ← mkFun
