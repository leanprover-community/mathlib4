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
| `TangentSpace% x`        | `TangentSpace I x`                  |
| `tangentMap[s] f`        | `tangentMapWithin I J f s`          |
| `tangentMap% f`          | `tangentMap I J f`                  |
| `UniqueMDiff[s]`         | `UniqueMDiffOn I s`                 |
| `UniqueMDiffAt[s] x`     | `UniqueMDiffWithinAt I s x`         |

In each of these cases, the models with corners are inferred from the domain and codomain of `f`.
The search for models with corners uses the local context and is (almost) only based on expression
structure, hence hopefully fast enough to always run.

Inferring models with corners supports all current `ModelWithCorners` instances in mathlib.
This will need to be updated as new instances are added.

For products of manifolds, we explicitly track if the resulting space is a product of normed spaces:
that case is ambiguous, and the elaborators would need to make a choice between e.g. the
trivial model with corners on a product `E × F` and the product of the trivial models on `E` and
`F`). If we encounter such an ambiguity, we warn about it and do not infer a model with corners.

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

## TODO

* try an opinionated strategy on products of normed spaces:
  is one guess correct more often than the other?
* alternatively, can the elaborator generate two `Try this` suggestions, corresponding to the
  possible options?
* not all those elaborators have corresponding delaborators yet, this should be fixed
* add elaborators for more notation
* make the model finding extensible, by converting it to an environment extension

If you would like to work on any of these, please coordinate with Michael Rothgang (@grunweg)
to avoid duplicating or conflicting work.

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

/-- Given `V : Expr` representing `E : B → Type*`, try to find a model fiber for `E`
by searching in local context for either a `FiberBundle F E` or
`TopologicalSpace (TotalSpace F E)` instance.

We could try a more systematic search of `TotalSpace F E` anywhere in the local context,
but the current heuristic is faster and sufficient so far. -/
private def findModelFiber? (V : Expr) : MetaM (Option Expr) := do
  withTraceNode `Elab.DiffGeo.TotalSpaceMk
    (fun _ ↦ do return m!"Searching for a model fiber for {← ppExpr V}") do
  trace[Elab.DiffGeo.TotalSpaceMk] "Searching for relevant `FiberBundle` instance in context"
  let f? ← findSomeLocalInstanceOf? `FiberBundle fun _ declType ↦ do
    /- Note: we do not use `match_expr` here since that would require importing
    `Mathlib.Topology.FiberBundle.Basic` to resolve `FiberBundle`. -/
    match declType with
    | mkApp7 (.const `FiberBundle _) _ F _ _ E _ _ => do
      if ← withReducible (pureIsDefEq E V) then
        trace[Elab.DiffGeo.TotalSpaceMk] "found `FiberBundle` instance for model fiber {← ppExpr F}"
        return some F
      else return none
    | _ => return none
  if f?.isSome then
    return f?
  else
    trace[Elab.DiffGeo.TotalSpaceMk] "Could not find a relevant `FiberBundle` instance in context"
    trace[Elab.DiffGeo.TotalSpaceMk] "Searching for a relevant \
      `TopologicalSpace (Bundle.TotalSpace _ _)` instance in context"
    return ← findSomeLocalInstanceOf? `TopologicalSpace fun _ declType ↦ do
      match declType with
      | mkApp (.const `TopologicalSpace _) (mkApp3 (.const `Bundle.TotalSpace _) _ F E) => do
        if ← withReducible (pureIsDefEq E V) then
          trace[Elab.DiffGeo.TotalSpaceMk] "It worked! model fiber is {← ppExpr F}"
          return some F
        else return none
      | _ => return none
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
        match ← findModelFiber? V with
        | some F =>
              let body ← mkAppM ``Bundle.TotalSpace.mk' #[F, x, (e.app x).headBeta]
              return (← mkLambdaFVars #[x] body).headBeta
        | none =>
          -- future: special-case `Bundle.TotalSpace` for V;
          -- if so, say "there is no need to apply T% twice"
          throwError "could not find a `FiberBundle` instance on `{V}`:\n\
          `{e}` is a function into `{V}`\n\n\
          hint: you may be missing suitable typeclass assumptions"
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

/-- Check if an expression `e` is a `ContinuousLinearMap` over an identity ring homomorphism where
the coefficient rings of the domain and codomain are reducibly definitionally equal. If so, we
return `(k, E, F)`, where `k` is the coefficient ring, `E` is the domain, and `F` is the codomain
of the continuous linear maps. Otherwise, we error.
Assumes that `e` is already in `whnf` and has had metavariables instantiated. -/
private def isCLMReduciblyDefeqCoefficients (e : Expr) : TermElabM <| Expr × Expr × Expr := do
  match_expr e with
  | ContinuousLinearMap k S _ _ σ E _ _ F _ _ _ _ =>
    trace[Elab.DiffGeo.MDiff] "`{e}` is a space of continuous (semi-)linear maps"
    unless ← withReducible <| pureIsDefEq k S do
      throwError "Coefficients `{k}` and `{S}` of `{e}` are not reducibly definitionally equal"
    match_expr ← whnfR σ with
    | RingHom.id _ _ => return (k, E, F)
    | _ => throwError "`{e}` is a space of continuous (semi-)linear maps over `{σ}`, \
      which is not the identity"
  | _ => throwError "`{e}` is not a space of continuous linear maps"

/--
Captures information when a model with corners is the trivial model on a normed space
(or on an inner product space, which is also a normed space):
contains the expressions describing the normed space and its base field.

Searching for a model with corners will return an `Option NormedSpaceInfo`,
which is `some` if and only if the trivial model on a normed space was found.
-/
structure NormedSpaceInfo where
  /-- The expression for the normed space itself. -/
  normedSpace : Expr
  /-- The expression for the normed space's base field. -/
  baseField   : Expr
deriving Inhabited

/--
Information about a model with corners found through `findModelInner`.
It includes the model with corners found, and, if this model is the trivial model with corners on a
normed space, information about that normed space. (Knowing this is important for forming products
of models.)

Most search results are not a model with corners for a normed space, so an `Expr` representing the
model with corners may be coerced directly to this type.
-/
structure FindModelResult where
  /-- Expression describing the model with corners found. -/
  model : Expr
  /-- Information on the underlying normed space,
  if this model is the trivial model with corners on a normed space. -/
  normedSpaceInfo? : Option NormedSpaceInfo := none
deriving Inhabited

instance : Coe Expr FindModelResult where
  coe model := { model }

/-- Try a strategy `x : TermElabM` which either successfully finds a `ModelWithCorners` or fails.
On failure in `x`, exceptions are caught, traced (`trace.Elab.DiffGeo.MDiff`), and `none` is
successfully returned.

We run `x` with `errToSorry == false` to convert elaboration errors into
exceptions, and under `withSynthesize` in order to force typeclass synthesis errors to appear and
be caught.

Trace messages produced during the execution of `x` are wrapped in a collapsible trace node titled
with `strategyDescr` and an indicator of success. -/
private def tryStrategy (strategyDescr : MessageData) (x : TermElabM FindModelResult) :
    TermElabM (Option FindModelResult) := do
  let s ← saveState
  try
    withTraceNode `Elab.DiffGeo.MDiff (fun _ => pure m!"{strategyDescr}") do
      let e ←
        try
          Term.withoutErrToSorry <| Term.withSynthesize x
        /- Catch the exception so that we can trace it, then throw it again to inform
        `withTraceNode` of the result. -/
        catch ex =>
          trace[Elab.DiffGeo.MDiff] "Failed with error:\n{ex.toMessageData}"
          throw ex
      trace[Elab.DiffGeo.MDiff] "Found model: `{e.model}`"
      if let some { normedSpace, baseField } := e.normedSpaceInfo? then
        trace[Elab.DiffGeo.MDiff] "This is the trivial model with corners for the normed space \
          `{normedSpace}` over the base field `{baseField}`."
      return e
  catch _ =>
    -- Restore infotrees to prevent any stale hovers, code actions, etc.
    -- Note that this does not break tracing, which saves each trace message's context.
    s.restore true
    return none

/-- Given an `Expr`ession `e`, try to find a `NormedSpace` instance on `e` and return the
underlying base field. Search local instances, before recursing into product and bundled
continuous linear maps. -/
partial def guessBaseFieldForNormedSpace (e : Expr) : TermElabM <| Option Expr := do
  if let some k ← findFromLocalInstance e then return k
  match_expr e with
  | Prod E _F =>
    guessBaseFieldForNormedSpace E
  | _ =>
    try
      let (_k, E, _F) ← isCLMReduciblyDefeqCoefficients e
      guessBaseFieldForNormedSpace E
    catch _e =>
      findFromLocalInstance e
where findFromLocalInstance (e : Expr) : TermElabM <| Option Expr := do
  findSomeLocalInstanceOf? ``NormedSpace fun _ type ↦ do
    match_expr type with
    | NormedSpace K E _ _ =>
      if ← withReducible (pureIsDefEq E e) then
        trace[Elab.DiffGeo.MDiff] "`{e}` is a normed field over `{K}`"; return some K
      else return none
    | _ => pure none

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
This method intentionally handles **neither** sums (disjoint unions) nor products of spaces,
nor an open subset of an existing manifold. These are handled in `findModel`.

Return an expression describing the found model with corners, together with information about
whether the model is the trivial model with corners on a normed space. (This is important for
forming products of models.)

Note that the matching on `e` does not see through reducibility (e.g. we distinguish the `abbrev`
`TangentBundle` from its definition), so `whnfR` should not be run on `e` prior to calling
`findModel` on it.

This implementation is not maximally robust yet.
-/
-- TODO: better error messages when all strategies fail
-- TODO: consider lowering monad to `MetaM`
partial def findModelInner (e : Expr) : TermElabM (Option FindModelResult) := do
  if let some m ← tryStrategy "TotalSpace"          fromTotalSpace      then return some m
  if let some m ← tryStrategy "TangentBundle"       fromTangentBundle   then return some m
  if let some m ← tryStrategy "NormedSpace"         fromNormedSpace     then return some m
  if let some m ← tryStrategy "Manifold"            fromManifold        then return some m
  if let some m ← tryStrategy "ContinuousLinearMap" fromCLM             then return some m
  if let some m ← tryStrategy "RealInterval"        fromRealInterval    then return some m
  if let some m ← tryStrategy "EuclideanSpace"      fromEuclideanSpace  then return some m
  if let some m ← tryStrategy "UpperHalfPlane"      fromUpperHalfPlane  then return some m
  if let some m ← tryStrategy "Units of algebra"    fromUnitsOfAlgebra  then return some m
  if let some m ← tryStrategy "Complex unit circle" fromCircle          then return some m
  if let some m ← tryStrategy "Sphere"              fromSphere          then return some m
  if let some m ← tryStrategy "NormedField"         fromNormedField     then return some m
  -- We run this strategy last, as it is the least likely to succeed.
  -- More commonly, we have a normed space on the nose, and `fromNormedSpace` should succeed.
  if let some m ← tryStrategy "InnerProductSpace" fromInnerProductSpace then return some m
  return none
where
  /- Note that errors thrown in the following are caught by `tryStrategy` and converted to trace
  messages. -/
  /-- Attempt to find a model from a `TotalSpace` first by seeing if it is the total space of a
  tangent bundle, and otherwise by finding a model with corners on its base. -/
  fromTotalSpace : TermElabM FindModelResult := do
    match_expr e with
    | Bundle.TotalSpace _ F V => do
      if let some m ← tryStrategy m!"TangentSpace" (fromTotalSpace.tangentSpace V) then return m
      trace[Elab.DiffGeo.MDiff]
        "{e} is the total space of a fiber bundle: trying to find a model on the base of `{V}`"
      -- `V` should be of type `B → Type*`, where `B` is the base of the vector bundle.
      -- Then, the desired model with corners is `I.prod (𝓘(𝕜, F))`, where `I` is the model on `B`
      -- and `𝕜` is the base field for `F`.
      let vtype ← whnf <| ← instantiateMVars <| ← inferType V
      trace[Elab.DiffGeo.MDiff] "`{V}` has type `{vtype}`"
      match vtype with
      | .forallE _x base _tgt _ =>
        let baseModel ← withTraceNode `Elab.DiffGeo.MDiff
            (fun _ ↦ pure m!"searching for a model with corners on the base `{base}`") do
          let some baseI ← findModelInner base
            | throwError m!"found no model with corners on the base {base} of `TotalSpace {F} {V}`"
          return baseI.model
        -- Very likely, `F` is a normed space over some field: let's see if `F` is a normed space
        -- on the nose.
        let some K ← guessBaseFieldForNormedSpace F
          | throwError "Couldn't find a `NormedSpace` structure on `{F}`"
        let tgtMod ← mkAppOptM ``modelWithCornersSelf #[K, none, F, none, none]
        mkAppM ``ModelWithCorners.prod  #[baseModel, tgtMod]
      | _ =>
        throwError s!"{e} is a TotalSpace {F} {V}, but {V} is not a pi type --- \
          could not infer base of the bundle"
    | _ => throwError "`{e}` is not a `Bundle.TotalSpace`."
  /-- Attempt to find a model from the total space of a tangent bundle. -/
  fromTotalSpace.tangentSpace (V : Expr) : TermElabM Expr := do
    match_expr V with
    | TangentSpace _k _ _E _ _ _H _ I M _ _ => do
      trace[Elab.DiffGeo.MDiff] "`{V}` is the total space of the `TangentBundle` of `{M}`"
      let srcIT : Term ← Term.exprToSyntax I
      let resTerm : Term ← ``(ModelWithCorners.tangent $srcIT)
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
  fromNormedSpace : TermElabM FindModelResult := do
    let some (inst, K) ← findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
        match_expr type with
        | NormedSpace K E _ _ =>
          if ← withReducible (pureIsDefEq E e) then return some (inst, K)
          else return none
        | _ => return none
      | throwError "Couldn't find a `NormedSpace` structure on `{e}` among local instances."
    trace[Elab.DiffGeo.MDiff] "`{e}` is a normed space over the field `{K}`"
    return {
      model := ← mkAppOptM ``modelWithCornersSelf #[K, none, e, none, inst]
      normedSpaceInfo? := some { normedSpace := e, baseField := K }
    }
  /-- Attempt to find the trivial model on an inner product space. -/
  fromInnerProductSpace : TermElabM FindModelResult := do
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
    return {
      model := ← mkAppOptM ``modelWithCornersSelf #[K, none, e, none, inst']
      normedSpaceInfo? := some { normedSpace := e, baseField := K }
    }
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
            return some H
          else if ← withReducible (pureIsDefEq H e) then
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
      | trace[Elab.DiffGeo.MDiff]
          "Couldn't find a `ModelWithCorners` with model space `{H}` in the local context."
        -- Try a normed space, and a normed field as last alternatives.
        let a ← findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
          match_expr type with
          | NormedSpace K E _ _ =>
            if ← withReducible (pureIsDefEq E H) then return some (inst, K)
            else return none
          | _ => return none
        if let some (inst, K) := a then
          trace[Elab.DiffGeo.MDiff] "`{H}` is a normed space over the field `{K}`"
          return ← mkAppOptM ``modelWithCornersSelf #[K, none, H, none, inst]
        trace[Elab.DiffGeo.MDiff] "Couldn't find a normed space structure on {H}` either: \
          assuming it is a non-trivially normed field"
        -- Return the trivial model with corners: this will work if `H` is a normed field.
        let eT : Term ← Term.exprToSyntax H
        let iTerm : Term ← ``(𝓘($eT))
        Term.elabTerm iTerm none
    return m
  /-- Attempt to find a model with corners on a space of continuous linear maps -/
  -- Note that (continuous) linear equivalences are not an abelian group, so are not a model with
  -- corners as a normed space. Merely linear maps are not a normed space either.
  fromCLM : TermElabM Expr := do
    -- If the coefficients of the codomain were a copy of `k` with a non-standard topology or smooth
    -- structure (such as, imposed deliberately through a type synonym), we do not want to infer
    -- the standard model with corners.
    -- Therefore, we only check definitional equality at reducible transparency.
    let (k, _E, _F) ← isCLMReduciblyDefeqCoefficients e
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
        let (k, V, W) ← isCLMReduciblyDefeqCoefficients α
        -- If `V` and `W` are not reducibly def-eq, the normed algebra instance should not fire:
        -- so it suffices to check at reducible transparency.
        if ← withReducible <| isDefEq V W then
          trace[Elab.DiffGeo.MDiff] "`{α}` is a space of continuous `{k}`-linear maps on `{V}`"
          let normedSpace? ← findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
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
          match normedSpace? with
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

set_option linter.style.emptyLine false in -- linter false positive
/-- Try to find a `ModelWithCorners` instance on a type (represented by an expression `e`),
using the local context to infer the appropriate instance.
This supports all `ModelWithCorners` instances that are currently defined in mathlib.
Further cases can be added as necessary.

Return an expression describing the found model with corners.

Note that the matching on `e` does not see through reducibility (e.g. we distinguish the `abbrev`
`TangentBundle` from its definition), so `whnfR` should not be run on `e` prior to calling
`findModel` on it.

This implementation is not maximally robust yet.
-/
-- TODO: better error messages when all strategies fail
-- TODO: consider lowering monad to `MetaM`

-- This function calls itself, which is why it is partial for now.
-- This should not be an issue in practice.
-- FIXME: can one prove this terminates w.r.t. a suitable measure? This is only recursing into
-- subexpressions (at least, after match_expr), right?
partial def findModel (e : Expr) : TermElabM Expr := do
  trace[Elab.DiffGeo.MDiff] "Finding a model with corners for: `{e}`"
  if let some { model .. } ← go e then
    return model
  else
    let tracing := (← isTracingEnabledFor `Elab.DiffGeo.MDiff)
    let hint : MessageData := if e.hasExprMVar then
      .hint' "the expected type contains metavariables, \
        maybe you need to provide an implicit argument"
      else if tracing then m!""
      else .hint' "failures to find a model with corners can be debugged with the \
          command `set_option trace.Elab.DiffGeo.MDiff true`."
    throwError "Could not find a model with corners for `{e}`.{hint}"
where
  go (e : Expr)  : TermElabM (Option FindModelResult) := do
    -- At first, try finding a model with corners on the space itself.
    if let some m ← findModelInner e then return some m
    -- Otherwise, we recurse into the expression,
    -- depending whether we have an open subset of a space, a product, or a direct sum of spaces.
    match_expr e with
    -- Check if `e` is an open subset of `M`, i.e. a `TopologicalSpace.Opens`.
    -- Because `e` is the result of coercing an actual `s : TopologicalSpace.Opens M` to a `Sort`
    -- via `Subtype`, the resulting expression `e` has a somewhat complicated form:
    -- `Subtype fun (x : M) => x ∈ s`.
    | Subtype _M p =>
      match (← instantiateMVars p).cleanupAnnotations with
      | .lam _x _ body _ =>
        match_expr body with
        | Membership.mem _ sType inst _ b =>
          unless b matches .bvar 0 do return none
          match_expr inst with
          | SetLike.instMembership _ _ _ =>
            match_expr sType with
            | TopologicalSpace.Opens M _ =>
              trace[Elab.DiffGeo.MDiff] "`{e}` is an open set of `{M}`, finding a model on `{M}`"
              -- `M` is not a open set of another manifold, as `Opens X` is (currently) not a
              -- topological space (and this would be strange). Therefore, do not recurse into `M`.
              go M
            | _ => return none
          | _ => return none
        | _ => return none
      | _ => return none
    | Prod E F =>
      trace[Elab.DiffGeo.MDiff] "Expression `{e}` is a product, recursing into each factor"
      let some { model := srcE, normedSpaceInfo? := normedSpaceE } ← go E
        | throwError "Found no model with corners on first factor `{E}`"
      let some { model := srcF, normedSpaceInfo? := normedSpaceF } ← go F
        | throwError "Found no model with corners on second factor `{F}`"
      -- If both E and F are normed spaces, we have ambiguity: warn and exit.
      if normedSpaceE.isSome && normedSpaceF.isSome then
        throwError "`{e}` is a product of normed spaces, so there are two potential models with \
        corners\nFor now, please specify the model by hand."
      -- Otherwise, we are not a normed space, and normally form the product model.
      let eTerm : Term ← Term.exprToSyntax srcE
      let fTerm : Term ← Term.exprToSyntax srcF
      let iTerm : Term ← ``(ModelWithCorners.prod $eTerm $fTerm)
      return some { model := ← Term.elabTerm iTerm none }
    | Sum E F =>
      trace[Elab.DiffGeo.MDiff] "Expression `{e}` is a direct sum of `{E}` and `{F}`\n\
        We assume the models match, and only look into the first summand"
      go E
    | _ => return none

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
    let tgtI ← findModel tgt
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

/-- `TangentSpace% x` elaborates to `TangentSpace I x`,
trying to determine `I` from the local context. -/
scoped elab:max "TangentSpace%" ppSpace x:term:arg : term => do
  let ex ← Term.elabTerm x none
  let extype ← instantiateMVars <| ← inferType ex
  let src ← findModel extype
  mkAppM ``TangentSpace #[src, ex]

/-- `tangentMap[s] f` elaborates to `tangentMapWithin I J f s`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "tangentMap[" s:term "]" ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef none
  mkAppM ``tangentMapWithin #[srcI, tgtI, ef, es]

/-- `tangentMap% f` elaborates to `tangentMap I J f`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "tangentMap%" ppSpace f:term:arg : term => do
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef none
  mkAppM ``tangentMap #[srcI, tgtI, ef]

/-- `UniqueMDiff[s]` elaborates to `UniqueMDiffOn I s`,
trying to determine `I` from the local context. -/
scoped elab:max "UniqueMDiff[" s:term "]" : term => do
  let es ← Term.elabTerm s none
  let estype : Expr ← inferType es
  match_expr estype with
  | Set α =>
    let I ← findModel α
    mkAppM ``UniqueMDiffOn #[I, es]
  | _ => throwError "`{es}` has type `{estype}` which is not of the form `Set α` for some `α`."

/-- `UniqueMDiffAt[s] x` elaborates to `UniqueMDiffWithinAt I s x`
trying to determine `I` from the local context.
The argument `x` can be omitted. -/
scoped elab:max "UniqueMDiffAt[" s:term "]" : term => do
  let es ← Term.elabTerm s none
  let estype : Expr ← inferType es
  match_expr estype with
  | Set α =>
    let I ← findModel α
    mkAppM ``UniqueMDiffWithinAt #[I, es]
  | _ => throwError "`{es}` has type `{estype}` which is not of the form `Set α` for some `α`."

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

/-!
### Delaborators

In this section we make sure the infoview also uses the above notation.
Not all elaborators are supported yet.
-/
section delaborators

namespace Manifold

open Bundle PrettyPrinter Delaborator SubExpr

/-- Delaborator for `Bundle.TotalSpace.mk` using anonymous constructor notation. -/
@[app_delab TotalSpace.mk] meta def delabTotalSpaceMk : Delab := do
  whenPPOption getPPNotation do
  withOverApp 5 do
  let bd ← withNaryArg 3 <| delab
  let vd ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

/-- Delaborator for `Bundle.TotalSpace.mk'` using anonymous constructor notation. -/
@[app_delab Bundle.TotalSpace.mk'] meta def delabTotalSpaceMkPrime : Delab := do
  whenPPOption getPPNotation do
  withOverApp 5 do
  let bd ← withNaryArg 3 <| delab
  let vd ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

/-- Delaborator for `mfderiv` using the custom elaborator, and special-casing
arguments that can use the `T%` elaborator. -/
@[app_delab mfderiv] meta def delabMFDeriv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let fe := (← getExpr).appArg!
    let .lam n _ b _ := fe | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withAppArg do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `(T% $σs) >>= annotateGoToSyntaxDef
    `(mfderiv% ($Tσs)) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withAppArg delab
    `(mfderiv% $fs) >>= annotateGoToSyntaxDef

-- TODO: add a delaborator for mfderivWithin (with a test)

/-- Delaborator for `MDifferentiable` using the custom elaborator, and special-casing
arguments that can use the `T%` elaborator. -/
@[app_delab MDifferentiable] meta def delabMDifferentiable : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let fe := (← getExpr).appArg!
    let .lam n _ b _ := fe | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withAppArg do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $σs)) >>= annotateGoToSyntaxDef
    `(MDiff $Tσs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withAppArg delab
    `(MDiff $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `MDifferentiableAt` using the custom elaborator, and special-casing
arguments that can use the `T%` elaborator. -/
@[app_delab MDifferentiableAt] meta def delabMDifferentiableAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 21 do
  try
    let fe := (← getExpr).appArg!
    let .lam n _ b _ := fe | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withAppArg do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $σs)) >>= annotateGoToSyntaxDef
    `(MDiffAt $Tσs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withAppArg delab
    `(MDiffAt $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `MDifferentiableOn` using the custom elaborator, and special-casing
arguments that can use the `T%` elaborator. -/
@[app_delab MDifferentiableOn] meta def delabMDifferentiableOn : Delab := do
  whenPPOption getPPNotation do
  withOverApp 22 do
  let ss ← withAppArg delab
  try
    let f := (← getExpr).getAppArgs[20]!
    let .lam n _ b _ := f | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let σe := b.getAppArgs[4]!.getAppFn
    guard <| σe.isFVar
    let Tσs ← withNaryArg 20 do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $σs)) >>= annotateGoToSyntaxDef
    `(MDiff[$ss] $Tσs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withNaryArg 20 <| delab
    `(MDiff[$ss] $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `MDifferentiableWithinAt` using the custom elaborator, and special-casing
arguments that can use the `T%` elaborator. -/
@[app_delab MDifferentiableWithinAt] meta def delabMDifferentiableWithinAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 22 do
  let ss ← withAppArg delab
  try
    let f := (← getExpr).getAppArgs[20]!
    let .lam n _ b _ := f | failure
    guard <| b.isAppOf ``Bundle.TotalSpace.mk'
    let s := b.getAppArgs[4]!.getAppFn
    guard <| s.isFVar
    let Tσs ← withNaryArg 20 do
      let σs ← withBindingBody n <| withNaryArg 4 <| withNaryFn delab
      `((T% $σs)) >>= annotateGoToSyntaxDef
    `(MDiffAt[$ss] $Tσs) >>= annotateGoToSyntaxDef
  catch _ =>
    let fs ← withNaryArg 20 <| delab
    `(MDiffAt[$ss] $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `UniqueMDiffOn` using the custom elaborator. -/
@[app_delab UniqueMDiffOn] meta def delabUniqueMDiffOn : Delab := do
  whenPPOption getPPNotation do
  withOverApp 12 do
  let ss ← withAppArg delab
  `(UniqueMDiff[$ss]) >>= annotateGoToSyntaxDef

/-- Delaborator for `UniqueMDiffWithinAt` using the custom elaborator. -/
@[app_delab UniqueMDiffWithinAt] meta def delabUniqueMDiffWithinAt : Delab := do
  whenPPOption getPPNotation do
  withOverApp 12 do
  let ss ← withAppArg delab
  `(UniqueMDiffAt[$ss]) >>= annotateGoToSyntaxDef

-- TODO: add more delaborators (and tests) for
-- ContMDiff, ContMDiffOn, ContMDiffAt, ContMDiffWithinAt, HasMFDerivAt, HasMFDerivWithinAt

-- TODO: when adding more elaborators, also add the corresponding delaborators

end Manifold

end delaborators
