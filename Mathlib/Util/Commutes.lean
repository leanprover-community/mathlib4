/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean
import Std.Data.Option.Basic
import Std.Tactic.Lint

/-!

# Auxiliary type class to avoid nested TC problems

This file defines a `[@Commutes C inst₁ inst₂]` type class meaning that the
instances `inst₁ : C` and `inst₂ : C` are defeq.  This allows us to write instances like:
```lean
instance [inst₁ : EuclideanDomain R] [inst₂ : Semiring R]
    [@Commutes (Semiring R) inst₂ (... inst₁ ...)] : @IsDomain R inst₂ :=
  ...
```
This instance can now be applied without synthesizing a `EuclideanDomain` instance.

We also define an `instance'` command automating this pattern.
See also https://github.com/leanprover/lean4/issues/1901

-/

namespace Mathlib.Util

set_option linter.unusedVariables false in
/--
Auxiliary type class stating that two type class instances commute.

Usually introduced using the `instance'` command.
-/
class inductive Commutes (α) : {inst₁ inst₂ : α} → Prop
  | mk : @Commutes α inst inst
attribute [instance] Commutes.mk

/-- Eliminates all `Commutes _` assumptions. -/
macro "elim_commutes" : tactic =>
  `(tactic| repeat cases ‹Commutes _›)

open Lean Elab Term Meta in
/--
Replaces all nonatomic instances in the type by fresh binders,
adding `Commutes` assumptions.  The resulting term is faster to apply in TC
resolution.  Used by the `instance'` command.

For example if `[AddCommMonoid A]` is in the local context,
then `commutify_type% (x + 0 = x)` returns
`∀ [HAdd A A A] [Commutes (HAdd A A A)] [Zero A] [Commutes (Zero A)], x + 0 = x`.
-/
elab "commutify_type% " e:term : term => do
  let e ← elabTerm e none
  forallTelescope e fun xs ty => do
  let (ty, repl) ← StateT.run (s := ({} : Lean.HashMap Expr Expr)) do
    Meta.transform ty
      (pre := fun
        | e@(.lam ..) =>
          if let some e := e.etaExpandedStrict? then
            return .visit e
          else
            return .done e
        | e@(.forallE ..) | e@(.letE ..) => return .done e
        | e => do
          if e.getAppFn.isFVar then
            return .done e
          else if let some _ ← isClass? (← inferType e) then
            return .done <| ← ((← get).find? e).getDM do
              let fvarid ← mkFreshFVarId
              modify (·.insert e (.fvar fvarid))
              return .fvar fvarid
          else
            return .continue e)
  let repl := repl.toArray
  withLocalDecls (← repl.mapM fun (e,_) =>
      return (← mkFreshUserName `inst, .instImplicit, fun _ => inferType e)) fun ys => do
  let ty := ty.replaceFVars (repl.map (·.2)) ys
  withLocalDecls (← (repl.zip ys).mapM fun ((e,_),y) =>
      return (← mkFreshUserName `commutes, .instImplicit, fun _ => do
        let t ← inferType e
        let u ← getLevel t
        return mkApp3 (.const ``Commutes [u]) t y e)) fun cs => do
  mkForallFVars (xs ++ ys ++ cs) ty

open private declValToTerm from Lean.Elab.MutualDef in
open Lean Elab Parser Command in
/--
Similar to `instance`, but generalizes nonatomic instance terms in the
conclusion.  Only use for `Prop`-valued classes.

Use for instance of: `CovariantClass`, `NoZeroDivisors`, `IsDomain`, etc.
-/
elab mods:declModifiers kind:attrKind tk:"instance'" prio:(namedPrio)?
    id0:(ppSpace declId)? sig:ppIndent(declSig) val:declVal : command => do
  let val : Term := ⟨← liftMacroM do declValToTerm val⟩
  let `(declSig| $bis* : $ty) := sig | throwUnsupportedSyntax
  let id ← id0.getDM do return mkIdentFrom tk (← mkInstanceName bis ty)
  elabCommand (← `($mods:declModifiers $kind:attrKind
    instance $[$prio]? $id $bis* : commutify_type% $ty :=
      by intros; elim_commutes; exact $val))
