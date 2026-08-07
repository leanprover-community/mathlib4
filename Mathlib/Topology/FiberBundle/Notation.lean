/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Thomas Murrills
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Notation for Elaborators for differential geometry

This file defines custom notation for vector bundles: we introduce an elaborator `T%` to ease
working with sections in a fibre bundle, scoped to the `Bundle` namespace.

It converts a section `s : Π x : B, V x` to a non-dependent function into the total space of the
bundle. (Mathematically, this is the same as post-composing with the inclusion map from each fiber
into the total space.)
```lean
-- omitted: let `V` be a fibre bundle over `B`

variable {σ : Π x : B, V x} in
#check T% σ -- `(fun x ↦ TotalSpace.mk' F x (σ x)) : M → TotalSpace F V`

-- Note how the name of the bound variable `x` is preserved.
variable {σ : (x : E) → Trivial E E' x} in
#check T% σ -- `(fun x ↦ TotalSpace.mk' E' x (σ x)) : E → TotalSpace E' (Trivial E E')`

variable {s : E → E'} in
#check T% s -- `(fun a ↦ TotalSpace.mk' E' a (s a)) : E → TotalSpace E' (Trivial E E')`
```

-/

public meta section

open scoped Bundle

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace Bundle.Elab

/- Note: these functions are convenient in this file, and may be convenient elsewhere, but their
precise behavior should be considered before adding them to the meta API. -/

/-- Finds the first local instance of class `c` for which `p inst type` produces `some a`.
Instantiates mvars in and runs `whnfR` on `type` before passing it to `p`. (Does not validate that
`c` resolves to a class.) -/
private def findSomeLocalInstanceOf? (c : Name) {α} (p : Expr → Expr → MetaM (Option α)) :
    MetaM (Option α) := do
  (← getLocalInstances).findSomeM? fun inst ↦ do
    if inst.className == c then
      let type ← whnfR <| ← instantiateMVars <| ← inferType inst.fvar
      p inst.fvar type
    else return none

/-- Finds the most recent local declaration for which `p fvar type` produces `some a`.
Skips implementation details; instantiates mvars in and runs `whnfR` on `type` before providing it
to `p`. -/
private def findSomeLocalHyp? {α} (p : Expr → Expr → MetaM (Option α)) : MetaM (Option α) := do
  (← getLCtx).findDeclRevM? fun decl ↦ do
    if decl.isImplementationDetail then return none
    let type ← whnfR <| ← instantiateMVars decl.type
    p decl.toExpr type

@[match_pattern, expose] def _root_.Lean.mkApp12 (f a b c d e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : Expr) :=
  mkApp6 (mkApp6 f a b c d e₁ e₂) e₃ e₄ e₅ e₆ e₇ e₈

/--
Utility for sections in a fibre bundle: if an expression `e` is a section
`s : Π x : M, V x` as a dependent function, convert it to a non-dependent function into the total
space. This handles the cases of
- sections of a trivial bundle
- vector fields on a manifold (i.e., sections of the tangent bundle)
- sections of an explicit fibre bundle
- turning a bare function `E → E'` into a section of the trivial bundle `Bundle.Trivial E E'`

This searches the local context for suitable hypotheses for the above cases by matching
on the expression structure, avoiding `isDefEq`. Therefore, it should be fast enough to always run.
This process can be traced with `set_option Elab.Bundle.TotalSpaceMk true`.

All applications of `e` in the resulting expression are beta-reduced.
If none of the handled cases apply, we simply return `e` (after beta-reducing).

This function is used for implementing the `T%` elaborator.
-/
-- TODO: document how this elaborator works, any gotchas, etc.
def totalSpaceMk (e : Expr) : MetaM Expr := do
  let etype ← whnf <| ← instantiateMVars <| ← inferType e
  match etype with
  | .forallE x base tgt _ => withLocalDeclD x base fun x ↦ do
    let tgtHasLooseBVars := tgt.hasLooseBVars
    let tgt := tgt.instantiate1 x
    -- Note: we do not run `whnfR` on `tgt` because `Bundle.Trivial` is reducible.
    /- Note: we do not use `match_expr` here since that would require importing
    `Mathlib.Geometry.Manifold.IsManifold.Basic` to resolve `TangentBundle`. -/
    match tgt with
    | mkApp3 (.const `Bundle.Trivial _) E E' _ => do
      trace[Elab.Bundle.TotalSpaceMk] "`{e}` is a section of `Bundle.Trivial {E} {E'}`"
      -- Note: we allow `isDefEq` here because any mvar assignments should persist.
      if ← withReducible (isDefEq E base) then
        let body ← mkAppM ``Bundle.TotalSpace.mk' #[E', x, (e.app x).headBeta]
        mkLambdaFVars #[x] body
      else return e
    | mkApp12 (.const `TangentSpace _) _k _ E _ _ _H _ _I M _ _ _x =>
      trace[Elab.Bundle.TotalSpaceMk] "`{e}` is a vector field on `{M}`"
      let body ← mkAppM ``Bundle.TotalSpace.mk' #[E, x, (e.app x).headBeta]
      mkLambdaFVars #[x] body
    | _ => match (← instantiateMVars tgt).cleanupAnnotations with
      | .app V _ =>
        trace[Elab.Bundle.TotalSpaceMk] "Section of a bundle as a dependent function"
        let f? ← findSomeLocalInstanceOf? `FiberBundle fun _ declType ↦
          /- Note: we do not use `match_expr` here since that would require importing
          `Mathlib.Topology.FiberBundle.Basic` to resolve `FiberBundle`. -/
          match declType with
          | mkApp7 (.const `FiberBundle _) _ F _ _ E _ _ => do
            if ← withReducible (pureIsDefEq E V) then
              let body ← mkAppM ``Bundle.TotalSpace.mk' #[F, x, (e.app x).headBeta]
              some <$> mkLambdaFVars #[x] body
            else return none
          | _ => return none
        return f?.getD e.headBeta
      | tgt =>
        trace[Elab.Bundle.TotalSpaceMk] "Section of a trivial bundle as a non-dependent function"
        -- TODO: can `tgt` depend on `x` in a way that is not a function application?
        -- Check that `x` is not a bound variable in `tgt`!
        if tgtHasLooseBVars then
          throwError "Attempted to fall back to creating a section of the trivial bundle out of \
            (`{e}` : `{etype}`) as a non-dependent function, but return type `{tgt}` depends on the
            bound variable (`{x}` : `{base}`).\n\
            Hint: applying the `T%` elaborator twice makes no sense."
        let trivBundle ← mkAppOptM ``Bundle.Trivial #[base, tgt]
        let body ← mkAppOptM ``Bundle.TotalSpace.mk' #[base, trivBundle, tgt, x, (e.app x).headBeta]
        mkLambdaFVars #[x] body
  | _ => return e.headBeta

end Elab

open Elab in
/--
Elaborator for sections in a fibre bundle: converts a section `s : Π x : M, V x` as a dependent
function to a non-dependent function into the total space. This handles the cases of
- sections of a trivial bundle
- vector fields on a manifold (i.e., sections of the tangent bundle)
- sections of an explicit fibre bundle
- turning a bare function `E → E'` into a section of the trivial bundle `Bundle.Trivial E E'`

This elaborator searches the local context for suitable hypotheses for the above cases by matching
on the expression structure, avoiding `isDefEq`. Therefore, it should be fast enough to always run.
The search can be traced with `set_option Elab.Bundle.TotalSpaceMk true`.
-/
scoped elab:max "T% " t:term:arg : term => do
  totalSpaceMk (← Term.elabTerm t none)

end Bundle

section trace

/-!
### Trace classes

Note that the overall `Elab` trace class does not inherit the trace classes defined in this
section, since they provide verbose information.
-/

/--
Trace class for the `T%` elaborator, which converts a section of a vector bundle as a dependent
function to a non-dependent function into the total space.
-/
initialize registerTraceClass `Elab.Bundle.TotalSpaceMk

end trace
