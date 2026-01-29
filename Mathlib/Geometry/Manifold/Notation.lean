/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Thomas Murrills
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-!
# Elaborators for differential geometry

This file defines custom elaborators for differential geometry to allow for more compact notation.
We introduce a class of elaborators for handling differentiability on manifolds, and the elaborator
`T%` for converting dependent sections of fibre bundles into non-dependent functions into the total
space.

All of these elaborators are scoped to the `Manifold` namespace.

## Differentiability on manifolds

We provide compact notation for differentiability and continuous differentiability on manifolds,
including inference of the model with corners.

| Notation                 | Elaborates to                       |
|--------------------------|-------------------------------------|
| `MDiff f`                | `MDifferentiable I J f`             |
| `MDiffAt f x`            | `MDifferentiableAt I J f x`         |
| `MDiff[u] f`             | `MDifferentiableOn I J f u`         |
| `MDiffAt[u] f x`         | `MDifferentiableWithinAt I J f u x` |
| `CMDiff n f`             | `ContMDiff I J n f`                 |
| `CMDiffAt n f x`         | `ContMDiffAt I J n f x`             |
| `CMDiff[u] n f`          | `ContMDiffOn I J n f u`             |
| `CMDiffAt[u] n f x`      | `ContMDiffWithinAt I J n f u x`     |
| `mfderiv[u] f x`         | `mfderivWithin I J f u x`           |
| `mfderiv% f x`           | `mfderiv I J f x`                   |
| `HasMFDerivAt[s] f x f'` | `HasMFDerivWithinAt I J f s x f'`   |
| `HasMFDerivAt% f x f'`   | `HasMFDerivAt I J f x f'`           |

In each of these cases, the models with corners are inferred from the domain and codomain of `f`.
The search for models with corners uses the local context and is (almost) only based on expression
structure, hence hopefully fast enough to always run.

This has no dedicated support for product manifolds (or product vector spaces) yet;
adding this is left for future changes. (It would need to make a choice between e.g. the
trivial model with corners on a product `E × F` and the product of the trivial models on `E` and
`F`). In these settings, the elaborators should be avoided (for now).

## `T%`

Secondly, this file adds an elaborator `T%` to ease working with sections in a fibre bundle,
which converts a section `s : Π x : M, V x` to a non-dependent function into the total space of the
bundle.
```lean
-- omitted: let `V` be a fibre bundle over `M`

variable {σ : Π x : M, V x} in
#check T% σ -- `(fun x ↦ TotalSpace.mk' F x (σ x)) : M → TotalSpace F V`

-- Note how the name of the bound variable `x` is preserved.
variable {σ : (x : E) → Trivial E E' x} in
#check T% σ -- `(fun x ↦ TotalSpace.mk' E' x (σ x)) : E → TotalSpace E' (Trivial E E')`

variable {s : E → E'} in
#check T% s -- `(fun a ↦ TotalSpace.mk' E' a (s a)) : E → TotalSpace E' (Trivial E E')`
```

---

These elaborators can be combined: `CMDiffAt[u] n (T% s) x`

**Warning.** These elaborators are a proof of concept; the implementation should be considered a
prototype. Don't rewrite all of mathlib to use it just yet. Notable limitations include
the following.

## TODO
- extend the elaborators to guess models with corners on product manifolds
  (this has to make a guess, hence cannot always be correct: but it could make the guess that
  is correct 90% of the time).
  For products of vector spaces `E × F`, this could print a warning about making a choice between
  the model in `E × F` and the product of the models on `E` and `F`.
- better error messages (as needed), with tests
- further testing and fixing of edge cases (with tests)
- add delaborators for these elaborators

-/

public meta section

open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic
open Mathlib.Tactic
open Qq

namespace Manifold.Elab

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
This process can be traced with `set_option Elab.DiffGeo.TotalSpaceMk true`.

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
    match_expr tgt with
    | Bundle.Trivial E E' _ =>
      trace[Elab.DiffGeo.TotalSpaceMk] "`{e}` is a section of `Bundle.Trivial {E} {E'}`"
      -- Note: we allow `isDefEq` here because any mvar assignments should persist.
      if ← withReducible (isDefEq E base) then
        let body ← mkAppM ``Bundle.TotalSpace.mk' #[E', x, (e.app x).headBeta]
        mkLambdaFVars #[x] body
      else return e
    | TangentSpace _k _ E _ _ _H _ _I M _ _ _x =>
      trace[Elab.DiffGeo.TotalSpaceMk] "`{e}` is a vector field on `{M}`"
      let body ← mkAppM ``Bundle.TotalSpace.mk' #[E, x, (e.app x).headBeta]
      mkLambdaFVars #[x] body
    | _ => match (← instantiateMVars tgt).cleanupAnnotations with
      | .app V _ =>
        trace[Elab.DiffGeo.TotalSpaceMk] "Section of a bundle as a dependent function"
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
        trace[Elab.DiffGeo.TotalSpaceMk] "Section of a trivial bundle as a non-dependent function"
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
The search can be traced with `set_option Elab.DiffGeo.TotalSpaceMk true`.
-/
scoped elab:max "T% " t:term:arg : term => do
  totalSpaceMk (← Term.elabTerm t none)

namespace Elab

/-- Try a strategy `x : TermElabM` which either successfully produces some `Expr` or fails. On
failure in `x`, exceptions are caught, traced (`trace.Elab.DiffGeo.MDiff`), and `none` is
successfully returned.

We run `x` with `errToSorry == false` to convert elaboration errors into
exceptions, and under `withSynthesize` in order to force typeclass synthesis errors to appear and
be caught.

Trace messages produced during the execution of `x` are wrapped in a collapsible trace node titled
with `strategyDescr` and an indicator of success. -/
private def tryStrategy (strategyDescr : MessageData) (x : TermElabM Expr) :
    TermElabM (Option Expr) := do
  let s ← saveState
  try
    withTraceNode `Elab.DiffGeo.MDiff (fun e => pure m!"{e.emoji} {strategyDescr}") do
      let e ←
        try
          Term.withoutErrToSorry <| Term.withSynthesize x
        /- Catch the exception so that we can trace it, then throw it again to inform
        `withTraceNode` of the result. -/
        catch ex =>
          trace[Elab.DiffGeo.MDiff] "Failed with error:\n{ex.toMessageData}"
          throw ex
      trace[Elab.DiffGeo.MDiff] "Found model: `{e}`"
      return e
  catch _ =>
    -- Restore infotrees to prevent any stale hovers, code actions, etc.
    -- Note that this does not break tracing, which saves each trace message's context.
    s.restore true
    return none

/-- Check if an expression `e` is (after instantiating metavariables and performing `whnf`),
a `ContinuousLinearMap` over an identity ring homomorphism and the coefficients of domain and
codomain are reducibly definitionally equal. If so, we return the coefficient field, the domain and
the codomain of the continuous linear maps (otherwise none). -/
def isCLMReduciblyDefeqCoefficients (e : Expr) : TermElabM <| Option <| Expr × Expr × Expr := do
  match_expr e with
    | ContinuousLinearMap k S _ _ _σ E _ _ F _ _ _ _ =>
      trace[Elab.DiffGeo.MDiff] "`{e}` is a space of continuous (semi-)linear maps"
      if ← withReducible <| isDefEq k S then
        -- TODO: check if σ is actually the identity!
        return some (k, E, F)
      else
        throwError "Coefficients `{k}` and `{S}` of `{e}` are not reducibly definitionally equal"
    | _ => return none

set_option linter.style.emptyLine false in -- linter false positive
/-- Try to find a `ModelWithCorners` instance on a type (represented by an expression `e`),
using the local context to infer the appropriate instance. This supports the following cases:
- the model with corners on the total space of a vector bundle
- the model with corners on the tangent space of a manifold
- a model with corners on a manifold, or on its underlying model space
- a closed interval of real numbers (including the unit interval)
- Euclidean space, Euclidean half-space and Euclidean quadrants
- a metric sphere in a real or complex inner product space
- the units of a normed algebra
- the complex upper half plane
- a space of continuous k-linear maps
- the trivial model `𝓘(𝕜, E)` on a normed space
- if the above are not found, try to find a `NontriviallyNormedField` instance on the type of `e`,
  and if successful, return `𝓘(𝕜)`.

Further cases can be added as necessary.

Return an expression describing the found model with corners.

`baseInfo` is only used for the first case, a model with corners on the total space of the vector
bundle. In this case, it contains a pair of expressions `(e, i)` describing the type of the base
and the model with corners on the base: these are required to construct the right model with
corners.

Note that the matching on `e` does not see through reducibility (e.g. we distinguish the `abbrev`
`TangentBundle` from its definition), so `whnfR` should not be run on `e` prior to calling
`findModel` on it.

This implementation is not maximally robust yet.
-/
-- TODO: better error messages when all strategies fail
-- TODO: consider lowering monad to `MetaM`
def findModel (e : Expr) (baseInfo : Option (Expr × Expr) := none) : TermElabM Expr := do
  trace[Elab.DiffGeo.MDiff] "Finding a model for: {e}"
  if let some m ← tryStrategy m!"TotalSpace"          fromTotalSpace     then return m
  if let some m ← tryStrategy m!"TangentBundle"       fromTangentBundle  then return m
  if let some m ← tryStrategy m!"NormedSpace"         fromNormedSpace    then return m
  if let some m ← tryStrategy m!"Manifold"            fromManifold       then return m
  if let some m ← tryStrategy m!"ContinuousLinearMap" fromCLM         then return m
  if let some m ← tryStrategy m!"RealInterval"        fromRealInterval   then return m
  if let some m ← tryStrategy m!"EuclideanSpace"      fromEuclideanSpace then return m
  if let some m ← tryStrategy m!"UpperHalfPlane"      fromUpperHalfPlane then return m
  if let some m ← tryStrategy m!"Units of algebra"    fromUnitsOfAlgebra then return m
  if let some m ← tryStrategy m!"Complex unit circle" fromCircle      then return m
  if let some m ← tryStrategy m!"Sphere"              fromSphere         then return m
  if let some m ← tryStrategy m!"NormedField"         fromNormedField    then return m
  if let some m ← tryStrategy m!"InnerProductSpace"   fromInnerProductSpace then return m
  throwError "Could not find a model with corners for `{e}`.

Hint: failures to find a model with corners can be debugged with the command \
`set_option trace.Elab.DiffGeo.MDiff true`."
where
  /- Note that errors thrown in the following are caught by `tryStrategy` and converted to trace
  messages. -/
  /-- Attempt to find a model from a `TotalSpace` first by attempting to use any provided
  `baseInfo`, then by seeing if it is the total space of a tangent bundle. -/
  fromTotalSpace : TermElabM Expr := do
    match_expr e with
    | Bundle.TotalSpace _ F V => do
      if let some m ← tryStrategy m!"From base info" (fromTotalSpace.fromBaseInfo F) then return m
      if let some m ← tryStrategy m!"TangentSpace" (fromTotalSpace.tangentSpace V) then return m
      throwError "Having a TotalSpace as source is not yet supported"
    | _ => throwError "`{e}` is not a `Bundle.TotalSpace`."
  /-- Attempt to use the provided `baseInfo` to find a model. -/
  fromTotalSpace.fromBaseInfo (F : Expr) : TermElabM Expr := do
    if let some (src, srcI) := baseInfo then
      trace[Elab.DiffGeo.MDiff] "Using base info `{src}`, `{srcI}`"
      let some K ← findSomeLocalInstanceOf? ``NormedSpace fun _ type ↦ do
          match_expr type with
          | NormedSpace K E _ _ =>
            if ← withReducible (pureIsDefEq E F) then
              trace[Elab.DiffGeo.MDiff] "`{F}` is a normed field over `{K}`"; return some K
            else return none
          | _ => return none
        | throwError "Couldn't find a `NormedSpace` structure on `{F}` among local instances."
      let kT : Term ← Term.exprToSyntax K
      let srcIT : Term ← Term.exprToSyntax srcI
      let FT : Term ← Term.exprToSyntax F
      let iTerm : Term ← ``(ModelWithCorners.prod $srcIT 𝓘($kT, $FT))
      Term.elabTerm iTerm none
    else
      throwError "No `baseInfo` provided"
  /-- Attempt to find a model from the total space of a tangent bundle. -/
  fromTotalSpace.tangentSpace (V : Expr) : TermElabM Expr := do
    match_expr V with
    | TangentSpace _k _ _E _ _ _H _ I M _ _ => do
      trace[Elab.DiffGeo.MDiff] "`{V}` is the total space of the `TangentBundle` of `{M}`"
      let srcIT : Term ← Term.exprToSyntax I
      let resTerm : Term ← ``(ModelWithCorners.prod $srcIT (ModelWithCorners.tangent $srcIT))
      Term.elabTerm resTerm none
    | _ => throwError "`{V}` is not a `TangentSpace`"
  /-- Attempt to find a model on a `TangentBundle` -/
  fromTangentBundle : TermElabM Expr := do
    match_expr e with
    | TangentBundle _k _ _E _ _ _H _ I M _ _ => do
      trace[Elab.DiffGeo.MDiff] "`{e}` is a `TangentBundle` over model `{I}` on `{M}`"
      let srcIT : Term ← Term.exprToSyntax I
      let resTerm : Term ← ``(ModelWithCorners.tangent $srcIT)
      Term.elabTerm resTerm none
    | _ => throwError "`{e}` is not a `TangentBundle`"
  /-- Attempt to find the trivial model on a normed space. -/
  fromNormedSpace : TermElabM Expr := do
    let some (inst, K) ← findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
        match_expr type with
        | NormedSpace K E _ _ =>
          if ← withReducible (pureIsDefEq E e) then return some (inst, K)
          else return none
        | _ => return none
      | throwError "Couldn't find a `NormedSpace` structure on `{e}` among local instances."
    trace[Elab.DiffGeo.MDiff] "`{e}` is a normed space over the field `{K}`"
    mkAppOptM ``modelWithCornersSelf #[K, none, e, none, inst]
  /-- Attempt to find the trivial model on an inner product space. -/
  fromInnerProductSpace : TermElabM Expr := do
    let some (inst, K) ← findSomeLocalInstanceOf? `InnerProductSpace fun inst type ↦ do
      -- We don't use `match_expr` here to avoid importing `InnerProductSpace`.
      match (← instantiateMVars type).cleanupAnnotations with
        | mkApp4 (.const `InnerProductSpace _) k E _ _ =>
          if ← withReducible (pureIsDefEq E e) then return some (inst, k)
          else return none
        | _ => return none
      | throwError "Couldn't find an `InnerProductSpace` structure on `{e}` among local instances."
    trace[Elab.DiffGeo.MDiff] "`{e}` is an inner product space over the field `{K}`"
    -- Convert the InnerProductSpace to a NormedSpace instance.
    let inst' ← mkAppOptM `InnerProductSpace.toNormedSpace #[K, e, none, none, inst]
    mkAppOptM ``modelWithCornersSelf #[K, none, e, none, inst']
  /-- Attempt to find a model with corners on a manifold, or on the charted space of a manifold. -/
  fromManifold : TermElabM Expr := do
    -- Return an expression for a type `H` (if any) such that `e` is a ChartedSpace over `H`,
    -- or `e` is `H` itself.
    let some H ← findSomeLocalInstanceOf? ``ChartedSpace fun inst type ↦ do
        trace[Elab.DiffGeo.MDiff] "considering instance of type `{type}`"
        match_expr type with
        | ChartedSpace H _ M _ =>
          if ← withReducible (pureIsDefEq M e) then
            trace[Elab.DiffGeo.MDiff] "`{e}` is a charted space over `{H}` via `{inst}`"
            return some H else
          if ← withReducible (pureIsDefEq H e) then
            trace[Elab.DiffGeo.MDiff] "`{e}` is the charted space of `{M}` via `{inst}`"
            return some H else return none
        | _ => return none
      | throwError "Couldn't find a `ChartedSpace` structure on `{e}` among local instances, \
          and `{e}` is not the charted space of some type in the local context either."
    let some m ← findSomeLocalHyp? fun fvar type ↦ do
        match_expr type with
        | ModelWithCorners _ _ _ _ _ H' _ => do
          if ← withReducible (pureIsDefEq H' H) then return some fvar else return none
        | _ => return none
      | throwError "Couldn't find a `ModelWithCorners` with model space `{H}` in the local context."
    return m
  /-- Attempt to find a model with corners on a space of continuous linear maps -/
  -- Note that (continuous) linear equivalences are not an abelian group, so are not a model with
  -- corners as a normed space. Merely linear maps are not a normed space either.
  fromCLM : TermElabM Expr := do
    -- If the coefficients of the codomain were a copy of `k` with a non-standard topology or smooth
    -- structure (such as, imposed deliberately through a type synonym), we do not want to infer
    -- the standard model with corners.
    -- Therefore, we only check definitional equality at reducible transparency.
    let some (k, _E, _F) ← isCLMReduciblyDefeqCoefficients e
      | throwError "`{e}` is not a space of continuous linear maps"
    let eK : Term ← Term.exprToSyntax k
    let eT : Term ← Term.exprToSyntax e
    let iTerm : Term ← ``(𝓘($eK, $eT))
    Term.elabTerm iTerm none
  /-- Attempt to find a model with corners on a Euclidean space, half-space or quadrant -/
  fromEuclideanSpace : TermElabM Expr := do
    -- We don't use `match_expr` to avoid importing `EuclideanHalfSpace`.
    match (← instantiateMVars e).cleanupAnnotations with
    | mkApp2 (.const `EuclideanSpace _) k _n =>
      let eK : Term ← Term.exprToSyntax k
      let eT : Term ← Term.exprToSyntax e
      Term.elabTerm (← ``(𝓘($eK, $eT))) none
    | mkApp2 (.const `EuclideanHalfSpace _) n _ =>
      mkAppOptM `modelWithCornersEuclideanHalfSpace #[n, none]
    | mkApp (.const `EuclideanQuadrant _) n =>
      mkAppOptM `modelWithCornersEuclideanQuadrant #[n]
    | _ => throwError "`{e}` is not a Euclidean space, half-space or quadrant"
  /-- Attempt to find a model with corners on a closed interval of real numbers,
  or on the unit interval of real numbers -/
  fromRealInterval : TermElabM Expr := do
    let some e := (← instantiateMVars e).cleanupAnnotations.coeTypeSet?
      | throwError "`{e}` is not a coercion of a set to a type"
    -- We don't use `match_expr` here to avoid importing `Set.Icc`.
    -- Note that `modelWithCornersEuclideanHalfSpace` is also not imported.
    match e with
    | Expr.const ``unitInterval [] =>
      trace[Elab.DiffGeo.MDiff] "`{e}` is the real unit interval"
      mkAppOptM `modelWithCornersEuclideanHalfSpace #[q(1 : ℕ), none]
    | mkApp4 (.const `Set.Icc _) α _ _x _y =>
      -- If `S` were a copy of `k` with a non-standard topology or smooth structure
      -- (such as, imposed deliberately through a type synonym), we do not want to infer
      -- the standard model with corners.
      -- Therefore, we only check definitional equality at reducible transparency.
      if ← withReducible <| isDefEq α q(ℝ) then
        -- We need not check if `x < y` is a fact in the local context: Lean will verify this
        -- itself when trying to synthesize a ChartedSpace instance.
        mkAppOptM `modelWithCornersEuclideanHalfSpace #[q(1 : ℕ), none]
      else throwError "`{e}` is a closed interval of type `{α}`, \
        which is not reducibly definitionally equal to ℝ"
    | _ => throwError "`{e}` is not a closed real interval"
  /-- Attempt to find a model with corners on the upper half plane in complex space -/
  fromUpperHalfPlane : TermElabM Expr := do
    -- We don't use `match_expr` to avoid importing `UpperHalfPlane`.
    if (← instantiateMVars e).cleanupAnnotations.isConstOf `UpperHalfPlane then
      let c ← Term.exprToSyntax (mkConst `Complex)
      Term.elabTerm (← `(𝓘($c))) none
    else throwError "`{e}` is not the complex upper half plane"
  /-- Attempt to find a model with corners on the units in a normed algebra -/
  fromUnitsOfAlgebra : TermElabM Expr := do
    match_expr e with
    | Units α _ =>
      trace[Elab.DiffGeo.MDiff] "`{e}` is the set of units on `{α}`"
      -- If `α` is a normed `𝕜`-algebra for some `𝕜`, we know a model with corners.
      -- We need to gather `𝕜` from the context: try to find a `NormedAlgebra` or `NormedSpace`
      -- instance in the local context.
      -- Note: this is somewhat brittle, and will need to be updated if other instance are made.
      -- A more robust solution would involve running typeclass inference,
      -- hence could potentially be slow.
      let searchNormedAlgebra ← findSomeLocalInstanceOf? ``NormedAlgebra fun inst type ↦ do
          trace[Elab.DiffGeo.MDiff] "considering instance of type `{type}`"
          match_expr type with
          | NormedAlgebra k R _ _ =>
            if ← withReducible (pureIsDefEq R α) then
              trace[Elab.DiffGeo.MDiff] "`{α}` is a normed algebra over `{k}` via `{inst}`"
              return some (k, R)
            else
              trace[Elab.DiffGeo.MDiff] "found a normed `{k}`-algebra structure on `{R}`, which \
              is not reducibly definitionally equal to `{α}`: continue the search"
              return none
          | _ => return none
      if let some (k, R) := searchNormedAlgebra then
        trace[Elab.DiffGeo.MDiff] "found a normed algebra: `{α}` is a normed `{k}`-algebra"
        let eK : Term ← Term.exprToSyntax k
        let eR : Term ← Term.exprToSyntax R
        Term.elabTerm (← ``(𝓘($eK, $eR))) none
      else
        trace[Elab.DiffGeo.MDiff] "`{α}` is not a normed algebra on the nose: try via a space of \
          continuous linear maps"
        -- If `α = V →L[𝕜] V` for a `𝕜`-normed space, we also have a normed algebra structure:
        -- search for such cases as well.
        match ← isCLMReduciblyDefeqCoefficients α with
        | none => throwError "`{α}` is not a space of continuous linear maps either"
        | some (k, V, W) =>
          -- If `V` and `W` are not reducibly def-eq, the normed algebra instance should not fire:
          -- so it suffices to check at reducible transparency.
          if ← withReducible <| isDefEq V W then
            trace[Elab.DiffGeo.MDiff] "`{α}` is a space of continuous `{k}`-linear maps on `{V}`"
            let searchNormedSpace := findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
              trace[Elab.DiffGeo.MDiff] "considering instances of type `{type}`"
              match_expr type with
              | NormedSpace k R _ _ =>
                -- We use reducible transparency to allow using a type synonym: this should not
                -- be unfolded.
                if ← withReducible (pureIsDefEq R V) then
                  trace[Elab.DiffGeo.MDiff] "`{V}` is a normed space over `{k}` via `{inst}`"
                  return some (k, R)
                else return none
              | _ => return none
            match ← searchNormedSpace with
            | some (k, _R) =>
              trace[Elab.DiffGeo.MDiff] "found a normed space: `{V}` is a normed space over `{k}`"
              let eK : Term ← Term.exprToSyntax k
              let eα : Term ← Term.exprToSyntax α
              Term.elabTerm (← ``(𝓘($eK, $eα))) none
            | _ => throwError  "Found no `NormedSpace` structure on `{V}` among local instances"
          else
            -- NB. If further instances of `NormedAlgebra` arise in practice, adding another check
            -- here is a good thing to do.
            -- NB. We don't know the field `𝕜` here, thus using typeclass inference to determine
            -- if `α` is a normed algebra is not a good idea. Searches `NormedAlgebra ?k α` for
            -- unspecified `k` often loop, and are not a good idea.
            throwError "{α}` is a space of continuous `{k}`-linear maps, but with domain `{V}` and \
              co-domain `{W}` being not definitionally equal"
    | _ => throwError "`{e}` is not a set of units, in particular not of a complete normed algebra"
  /-- Attempt to find a model with corners on the complex unit circle -/
  fromCircle : TermElabM Expr := do
    -- We don't use `match_expr` to avoid importing `Circle`.
    if (← instantiateMVars e).cleanupAnnotations.isConstOf `Circle then
      -- We have not imported `EuclideanSpace` yet, so build an expression by hand.
      let r ← Term.exprToSyntax q(ℝ)
      let eE ← Term.exprToSyntax <| ← mkAppM `EuclideanSpace #[q(ℝ), q(Fin 1)]
      Term.elabTerm (← ``(𝓘($r, $eE))) none
    else throwError "`{e}` is not the complex unit circle"
  /-- Attempt to find a model with corners on a metric sphere in a real normed space -/
  fromSphere : TermElabM Expr := do
    let some e := (← instantiateMVars e).cleanupAnnotations.coeTypeSet?
      | throwError "`{e}` is not a coercion of a set to a type"
    match_expr e with
    | Metric.sphere α _ _x _r =>
      trace[Elab.DiffGeo.MDiff] "`{e}` is a metric sphere in `{α}`"
      -- Attempt to find a real or complex inner product space instance on `α`.
      let searchIPSpace := findSomeLocalInstanceOf? `InnerProductSpace fun inst type ↦ do
          trace[Elab.DiffGeo.MDiff] "considering instance of type `{type}`"
          -- We don't use `match_expr` here to avoid importing `InnerProductSpace`.
          match type with
          | mkApp4 (.const `InnerProductSpace _) k E _ _ =>
            -- We use reducible transparency to allow using a type synonym: this should not
            -- be unfolded.
            if ← withReducible (pureIsDefEq E α) then
              trace[Elab.DiffGeo.MDiff] "`{α}` is a `{k}`-inner product space via `{inst}`"
              return some E
            else
              trace[Elab.DiffGeo.MDiff] "found an inner product space on `{E}`, which \
                is not reducibly definitionally equal to `{α}`: continue the search"
              return none
          | _ => return none
      let factFinder (E : Expr) := findSomeLocalInstanceOf? ``Fact fun _inst type ↦ do
        trace[Elab.DiffGeo.MDiff] "considering instance of type `{type}`"
        match_expr type with
        | Fact a =>
          trace[Elab.DiffGeo.MDiff] "considering fact of kind `{a}`"
          match_expr a with
          | Eq _ lhs rhs =>
            match_expr lhs with
            | Module.finrank R F _ _ _ =>
              -- We use reducible transparency to allow using a type synonym: this should not
              -- be unfolded.
              if ← withReducible (pureIsDefEq R q(ℝ) <&&> pureIsDefEq E F) then
                trace[Elab.DiffGeo.MDiff] "found a fact about `finrank ℝ E` via `{_inst}`"
                -- Try to unify the rhs with an expression m + 1, for a natural number m.
                -- If we find one, that's the dimension of our model with corners.
                -- Always returning the finrank - 1 would be undesirable, for instance since natural
                -- number subtraction is badly behaved.
                have rhs : Q(ℕ) := rhs
                match rhs with
                | ~q($n + 1) =>
                  trace[Elab.DiffGeo.MDiff] "rhs `{rhs}` is `{n}` + 1"
                  return some n
                | _ =>
                  throwError "found a fact about `finrank ℝ E`, but the right hand \
                    side `{rhs}` is not of the form `m + 1` for some `m`"
              else
                trace[Elab.DiffGeo.MDiff] "found a fact about finrank, \
                  but not about `finrank ℝ E`: continue the search"
                return none
            | _ => return none
          | _ => return none
        | _ => return none
      if let some E ← searchIPSpace then
        -- We found a sphere in the inner product space `E`:
        -- search for a `Fact (finrank ℝ E) = m + 1`,
        -- then the sphere is `m`-dimensional, and `modelEuclideanSpace m` is our model.
        let some nE ← factFinder E
          | throwError "Found no fact `finrank ℝ {E} = n + 1` in the local context"
        -- We have not imported `EuclideanSpace` yet, so build an expression by hand.
        let r ← Term.exprToSyntax q(ℝ)
        let eE ← Term.exprToSyntax <| ← mkAppM `EuclideanSpace #[q(ℝ), q(Fin $nE)]
        Term.elabTerm (← ``(𝓘($r, $eE))) none
      else throwError "found no real normed space instance on `{α}`"
    | _ => throwError "`{e}` is not a sphere in a real normed space"
  /-- Attempt to find a model with corners from a normed field.
  We attempt to find a global instance here. -/
  fromNormedField : TermElabM Expr := do
    let eT : Term ← Term.exprToSyntax e
    let iTerm : Term ← ``(𝓘($eT, $eT))
    Term.elabTerm iTerm none

/-- If the type of `e` is a non-dependent function between spaces `src` and `tgt`, try to find a
model with corners on both `src` and `tgt`. If successful, return both models.

We pass `e` instead of just its type for better diagnostics.

If `es` is `some`, we verify that `src` and the type of `es` are definitionally equal. -/
def findModels (e : Expr) (es : Option Expr) : TermElabM (Expr × Expr) := do
  let etype ← whnf <| ← instantiateMVars <| ← inferType e
  match etype with
  | .forallE _ src tgt _ =>
    if tgt.hasLooseBVars then
      -- TODO: try `T%` here, and if it works, add an interactive suggestion to use it
      throwError "Term `{e}` is a dependent function, of type `{etype}`\nHint: you can use \
        the `T%` elaborator to convert a dependent function to a non-dependent one"
    let srcI ← findModel src
    if let some es := es then
      let estype ← inferType es
      /- Note: we use `isDefEq` here since persistent metavariable assignments in `src` and
      `estype` are acceptable.
      TODO: consider attempting to coerce `es` to a `Set`. -/
      if !(← isDefEq estype <| ← mkAppM ``Set #[src]) then
        throwError "The domain `{src}` of `{e}` is not definitionally equal to the carrier type of \
          the set `{es}` : `{estype}`"
    let tgtI ← findModel tgt (src, srcI)
    return (srcI, tgtI)
  | _ => throwError "Expected{indentD e}\nof type{indentD etype}\nto be a function"

end Elab

open Elab

/-- `MDiffAt[s] f x` elaborates to `MDifferentiableWithinAt I J f s x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
scoped elab:max "MDiffAt[" s:term "]" ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← ensureIsFunction <| ← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``MDifferentiableWithinAt #[srcI, tgtI, ef, es]

/-- `MDiffAt f x` elaborates to `MDifferentiableAt I J f x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
scoped elab:max "MDiffAt" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``MDifferentiableAt #[srcI, tgtI, e]

-- An alternate implementation for `MDiffAt`.
-- /-- `MDiffAt2 f x` elaborates to `MDifferentiableAt I J f x`,
-- trying to determine `I` and `J` from the local context.
-- The argument `x` can be omitted. -/
-- scoped elab:max "MDiffAt2" ppSpace t:term:arg : term => do
--   let e ← Term.elabTerm t none
--   let etype ← whnfR <| ← instantiateMVars <| ← inferType e
--   forallBoundedTelescope etype (some 1) fun src tgt ↦ do
--     if let some src := src[0]? then
--       let srcI ← findModel (← inferType src)
--       if Lean.Expr.occurs src tgt then
--         throwErrorAt t "Term `{e}` is a dependent function, of type `{etype}`\n\
--         Hint: you can use the `T%` elaborator to convert a dependent function \
--         to a non-dependent one"
--       let tgtI ← findModel tgt (src, srcI)
--       mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
--     else
--       throwErrorAt t "Expected{indentD e}\nof type{indentD etype}\nto be a function"

/-- `MDiff[s] f` elaborates to `MDifferentiableOn I J f s`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "MDiff[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let et ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, tgtI) ← findModels et es
  mkAppM ``MDifferentiableOn #[srcI, tgtI, et, es]

/-- `MDiff f` elaborates to `MDifferentiable I J f`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "MDiff" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``MDifferentiable #[srcI, tgtI, e]

-- We ensure the type of `n` before checking `f` is a function to provide better error messages
-- in case e.g. `f` and `n` are swapped.
-- TODO: provide better error messages if just `n` is forgotten (say, by making `n` optional in
-- the parser and erroring later in the elaborator); currently, this yields just a parser error.

/-- `CMDiffAt[s] n f x` elaborates to `ContMDiffWithinAt I J n f s x`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
scoped elab:max "CMDiffAt[" s:term "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let ef ← ensureIsFunction <| ← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``ContMDiffWithinAt #[srcI, tgtI, ne, ef, es]

/-- `CMDiffAt n f x` elaborates to `ContMDiffAt I J n f x`
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
scoped elab:max "CMDiffAt" ppSpace nt:term:arg ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let (srcI, tgtI) ← findModels e none
  mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]

/-- `CMDiff[s] n f` elaborates to `ContMDiffOn I J n f s`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
scoped elab:max "CMDiff[" s:term "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let ef ← ensureIsFunction <| ← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``ContMDiffOn #[srcI, tgtI, ne, ef, es]

/-- `CMDiff n f` elaborates to `ContMDiff I J n f`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
scoped elab:max "CMDiff" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let e ← ensureIsFunction <| ← Term.elabTerm f none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``ContMDiff #[srcI, tgtI, ne, e]

/-- `mfderiv[u] f x` elaborates to `mfderivWithin I J f u x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "mfderiv[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e es
  mkAppM ``mfderivWithin #[srcI, tgtI, e, es]

/-- `mfderiv% f x` elaborates to `mfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "mfderiv%" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <| ← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``mfderiv #[srcI, tgtI, e]

/-- `HasMFDerivAt[s] f x f'` elaborates to `HasMFDerivWithinAt I J f s x f'`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "HasMFDerivAt[" s:term "]" ppSpace
    f:term:arg ppSpace x:term:arg ppSpace f':term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let ex ← Term.elabTerm x none
  let ef' ← Term.elabTerm f' none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``HasMFDerivWithinAt #[srcI, tgtI, ef, es, ex, ef']

/-- `HasMFDerivAt% f x f'` elaborates to `HasMFDerivAt I J f x f'`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "HasMFDerivAt%" ppSpace
    f:term:arg ppSpace x:term:arg ppSpace f':term:arg : term => do
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let ex ← Term.elabTerm x none
  let ef' ← Term.elabTerm f' none
  let (srcI, tgtI) ← findModels ef none
  mkAppM ``HasMFDerivAt #[srcI, tgtI, ef, ex, ef']

end Manifold

section trace

/-!
### Trace classes

Note that the overall `Elab` trace class does not inherit the trace classes defined in this
section, since they provide verbose information.
-/

/--
Trace class for differential geometry elaborators. Setting this to `true` traces elaboration
for the `T%` elaborator (`trace.Elab.DiffGeo.TotalSpaceMk`) and the family of `MDiff`-like
elaborators (`trace.Elab.DiffGeo.MDiff`).
-/
initialize registerTraceClass `Elab.DiffGeo

/--
Trace class for the `T%` elaborator, which converts a section of a vector bundle as a dependent
function to a non-dependent function into the total space.
-/
initialize registerTraceClass `Elab.DiffGeo.TotalSpaceMk (inherited := true)

/--
Trace class for the `MDiff` elaborator and friends, which infer a model with corners on the domain
(resp. codomain) of the map in question.
-/
initialize registerTraceClass `Elab.DiffGeo.MDiff (inherited := true)

end trace
