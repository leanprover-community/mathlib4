/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Thomas Murrills
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs
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

| Notation            | Elaborates to                       |
|---------------------|-------------------------------------|
| `MDiff f`           | `MDifferentiable I J f`             |
| `MDiffAt f x`       | `MDifferentiableAt I J f x`         |
| `MDiff[u] f`        | `MDifferentiableOn I J f u`         |
| `MDiffAt[u] f x`    | `MDifferentiableWithinAt I J f u x` |
| `CMDiff n f`        | `ContMDiff I J n f`                 |
| `CMDiffAt n f x`    | `ContMDiffAt I J n f x`             |
| `CMDiff[u] n f`     | `ContMDiffOn I J n f u`             |
| `CMDiffAt[u] n f x` | `ContMDiffWithinAt I J n f u x`     |
| `mfderiv[u] f x`    | `mfderivWithin I J f u x`           |
| `mfderiv% f x`      | `mfderiv I J f x`                   |

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
      let type ← whnfR <|← instantiateMVars <|← inferType inst.fvar
      p inst.fvar type
    else return none

/-- Finds the most recent local declaration for which `p fvar type` produces `some a`.
Skips implementation details; instantiates mvars in and runs `whnfR` on `type` before providing it
to `p`. -/
private def findSomeLocalHyp? {α} (p : Expr → Expr → MetaM (Option α)) : MetaM (Option α) := do
  (← getLCtx).findDeclRevM? fun decl ↦ do
    if decl.isImplementationDetail then return none
    let type ← whnfR <|← instantiateMVars decl.type
    p decl.toExpr type

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
on the expression structure, avoiding `isDefEq`. Therefore, it is (hopefully) fast enough to always
run.
-/
-- TODO: document how this elaborator works, any gotchas, etc.
-- TODO: factor out `MetaM` component for reuse
scoped elab:max "T% " t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← whnf <|← instantiateMVars <|← inferType e
  match etype with
  | .forallE x base tgt _ => withLocalDeclD x base fun x ↦ do
    let tgtHasLooseBVars := tgt.hasLooseBVars
    let tgt := tgt.instantiate1 x
    -- Note: we do not run `whnfR` on `tgt` because `Bundle.Trivial` is reducible.
    match_expr tgt with
    | Bundle.Trivial E E' _ =>
      trace[Elab.DiffGeo.TotalSpaceMk] "Section of a trivial bundle"
      -- Note: we allow `isDefEq` here because any mvar assignments should persist.
      if ← withReducible (isDefEq E base) then
        let body ← mkAppM ``Bundle.TotalSpace.mk' #[E', x, e.app x]
        mkLambdaFVars #[x] body
      else return e
    | TangentSpace _k _ E _ _ _H _ _I _M _ _ _x =>
      trace[Elab.DiffGeo.TotalSpaceMk] "Vector field"
      let body ← mkAppM ``Bundle.TotalSpace.mk' #[E, x, e.app x]
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
              let body ← mkAppM ``Bundle.TotalSpace.mk' #[F, x, e.app x]
              some <$> mkLambdaFVars #[x] body
            else return none
          | _ => return none
        return f?.getD e
      | tgt =>
        trace[Elab.DiffGeo.TotalSpaceMk] "Section of a trivial bundle as a non-dependent function"
        -- TODO: can `tgt` depend on `x` in a way that is not a function application?
        -- Check that `x` is not a bound variable in `tgt`!
        if tgtHasLooseBVars then
          throwError "Attempted to fall back to creating a section of the trivial bundle out of \
            ({e} : {etype}) as a non-dependent function, but return type {tgt} depends on the bound
            variable ({x} : {base}).\nHint: applying the `T%` elaborator twice makes no sense."
        let trivBundle ← mkAppOptM ``Bundle.Trivial #[base, tgt]
        let body ← mkAppOptM ``Bundle.TotalSpace.mk' #[base, trivBundle, tgt, x, e.app x]
        mkLambdaFVars #[x] body
  | _ => return e

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
      trace[Elab.DiffGeo.MDiff] "Found model: {e}"
      return e
  catch _ =>
    -- Restore infotrees to prevent any stale hovers, code actions, etc.
    -- Note that this does not break tracing, which saves each trace message's context.
    s.restore true
    return none

/-- Workhorse method for `findModel`: try all strategies, and return the first one which succeeded.
This method tries all strategies for single spaces (i.e., does not recurse into products).

On succcess, return `some (e × eN)`, where `e` is an `Expr` for the type it found, and `eN` is
`some E` if `e` is a normed space `E` (and `none`) otherwise.
This information is used to assign models to products of normed spaces currently. -/
def findModelInner (e : Expr) (baseInfo : Option (Expr × Expr) := none) :
    TermElabM <| Option (Expr × Bool) := do
  if let some m ← tryStrategy m!"TotalSpace"     fromTotalSpace     then return some (m, false)
  if let some m ← tryStrategy m!"TangentBundle"  fromTangentBundle  then return some (m, false)
  -- TODO: make fromNormedSpace return the expression `E` also... then return it
  if let some m ← tryStrategy m!"NormedSpace"    fromNormedSpace    then return some (m, true)
  if let some m ← tryStrategy m!"Manifold"       fromManifold       then return some (m, false)
  if let some m ← tryStrategy m!"ContinuousLinearMap" fromCLM       then return some (m, false)
  if let some m ← tryStrategy m!"RealInterval"   fromRealInterval   then return some (m, false)
  if let some m ← tryStrategy m!"UpperHalfPlane" fromUpperHalfPlane then return some (m, false)
  if let some m ← tryStrategy m!"NormedField"    fromNormedField    then return some (m, false)
  return none
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
    | _ => throwError "{e} is not a `Bundle.TotalSpace`."
  /-- Attempt to use the provided `baseInfo` to find a model. -/
  fromTotalSpace.fromBaseInfo (F : Expr) : TermElabM Expr := do
    if let some (src, srcI) := baseInfo then
      trace[Elab.DiffGeo.MDiff] "Using base info {src}, {srcI}"
      let some K ← findSomeLocalInstanceOf? ``NormedSpace fun _ type ↦ do
          match_expr type with
          | NormedSpace K E _ _ =>
            if ← withReducible (pureIsDefEq E F) then return some K else return none
          | _ => return none
        | throwError "Couldn't find a `NormedSpace` structure on {F} among local instances."
      trace[Elab.DiffGeo.MDiff] "{F} is a normed field over {K}"
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
      trace[Elab.DiffGeo.MDiff] "This is the total space of the tangent bundle of {M}"
      let srcIT : Term ← Term.exprToSyntax I
      let resTerm : Term ← ``(ModelWithCorners.prod $srcIT (ModelWithCorners.tangent $srcIT))
      Term.elabTerm resTerm none
    | _ => throwError "{V} is not a `TangentSpace`"
  /-- Attempt to find a model on a `TangentBundle` -/
  fromTangentBundle : TermElabM Expr := do
    match_expr e with
    | TangentBundle _k _ _E _ _ _H _ I M _ _ => do
      trace[Elab.DiffGeo.MDiff] "{e} is a TangentBundle over model {I} on {M}"
      let srcIT : Term ← Term.exprToSyntax I
      let resTerm : Term ← ``(ModelWithCorners.tangent $srcIT)
      Term.elabTerm resTerm none
    | _ => throwError "{e} is not a `TangentBundle`"
  /-- Attempt to find the trivial model on a normed space. -/
  fromNormedSpace : TermElabM (Expr × Option (Expr × Expr)) := do
    let some (inst, K) ← findSomeLocalInstanceOf? ``NormedSpace fun inst type ↦ do
        match_expr type with
        | NormedSpace K E _ _ =>
          if ← withReducible (pureIsDefEq E e) then return some (inst, K) else return none
        | _ => return none
      | throwError "Couldn't find a `NormedSpace` structure on {e} among local instances."
    trace[Elab.DiffGeo.MDiff] "Field is: {K}"
    return (← mkAppOptM ``modelWithCornersSelf #[K, none, e, none, inst], some (K, e))
  /-- Attempt to find a model with corners on a manifold, or on the charted space of a manifold. -/
  fromManifold : TermElabM Expr := do
    -- Return an expression for a type `H` (if any) such that `e` is a ChartedSpace over `H`,
    -- or `e` is `H` itself.
    let some H ← findSomeLocalInstanceOf? ``ChartedSpace fun _ type ↦ do
        trace[Elab.DiffGeo.MDiff] "found a `ChartedSpace` instance: `{type}`"
        match_expr type with
        | ChartedSpace H _ M _ =>
          if ← withReducible (pureIsDefEq M e) then return some H else
          if ← withReducible (pureIsDefEq H e) then return some H else return none
        | _ => return none
      | throwError "Couldn't find a `ChartedSpace` structure on {e} among local instances,\n\
        and {e} is not the charted space of some type in the local context either."
    let some m ← findSomeLocalHyp? fun fvar type ↦ do
        match_expr type with
        | ModelWithCorners _ _ _ _ _ H' _ => do
          if ← withReducible (pureIsDefEq H' H) then return some fvar else return none
        | _ => return none
      | throwError "Couldn't find a `ModelWithCorners` with model space {H} in the local context."
    return m
  /-- Attempt to find a model with corners on a space of continuous linear maps -/
  -- TODO: should this also support continuous linear equivalences?
  fromCLM : TermElabM Expr := do
    match_expr e with
    | ContinuousLinearMap k S _ _ _σ _E _ _ _F _ _  _ _ =>
      if ← isDefEq k S then
        -- TODO: check if σ is actually the identity!
        let eK : Term ← Term.exprToSyntax k
        let eT : Term ← Term.exprToSyntax e
        let iTerm : Term := ← ``(𝓘($eK, $eT))
        Term.elabTerm iTerm none
      else
        throwError "Coefficients {k} and {S} of {e} are not definitionally equal"
    -- | ContinuousLinearEquiv k S _ _ _σ _σ' _ _ _E _ _ _F _ _ _ _ =>
    --   if ← isDefEq k S then
    --     -- TODO: check if σ is actually the identity!
    --     let eK : Term ← Term.exprToSyntax k
    --     let eT : Term ← Term.exprToSyntax e
    --     let iTerm : Term := ← ``(𝓘($eK, $eT))
    --     Term.elabTerm iTerm none
    --   else
    --     throwError "Coefficients {k} and {S} of {e} are not definitionally equal"
    | _ => throwError "{e} is not a space of continuous linear maps"
  /-- Attempt to find a model with corners on a closed interval of real numbers -/
  fromRealInterval : TermElabM Expr := do
    let some e := (← instantiateMVars e).cleanupAnnotations.coeTypeSet?
      | throwError "{e} is not a coercion of a set to a type"
    match e with
    | mkApp4 (.const `Set.Icc _) α _ _x _y =>
      if ← isDefEq α q(ℝ) then
        -- We need not check if `x < y` is a fact in the local context: Lean will verify this
        -- itself when trying to synthesize a ChartedSpace instance.
        mkAppOptM `modelWithCornersEuclideanHalfSpace #[q(1 : ℕ), none]
      else throwError "{e} is a closed interval of type {α}, which is not definitially equal to ℝ"
    | _ => throwError "{e} is not a closed real interval"
  /-- Attempt to find a model with corners on the upper half plane in complex space -/
  fromUpperHalfPlane : TermElabM Expr := do
    if (← instantiateMVars e).cleanupAnnotations.isConstOf `UpperHalfPlane then
      let c ← Term.exprToSyntax (mkConst `Complex)
      Term.elabTerm (← `(𝓘($c))) none
    else throwError "{e} is not the complex upper half plane"
  /-- Attempt to find a model with corners from a normed field. We attempt to find a global
  instance here. -/
  fromNormedField : TermElabM Expr := do
    let eT : Term ← Term.exprToSyntax e
    let iTerm : Term ← ``(𝓘($eT, $eT))
    Term.elabTerm iTerm none


/-- Try to find a `ModelWithCorners` instance on a type (represented by an expression `e`),
using the local context to infer the appropriate instance. This supports the following cases:
- the model with corners on the total space of a vector bundle
- the model with corners on the tangent space of a manifold
- a model with corners on a manifold, or on its underlying model space
- a closed interval of real numbers
- the complex upper half plane
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
  -- At first, try finding a model on the space itself.
  if let some (m, _) ← findModelInner e baseInfo then return m
  -- TODO: allow arbitrarily many factors by writing a proper recursive definition!
  match_expr e with
  | Prod src tgt =>
    trace[Elab.DiffGeo.MDiff] "Expression {e} is a product, recursing into each factor"
    let some (srcI, normedSpacesOnlyI) := ← findModelInner src baseInfo
      | match_expr src with
        | Prod src1 src2 =>
          trace[Elab.DiffGeo.MDiff] "Expression {src} is a product, recursing into each factor"
          let some res1 := ← findModelInner src1 baseInfo
            | throwError "Found no model with corners on {src1}"
          let some res2 := ← findModelInner src1 baseInfo
            | throwError "Found no model with corners on {src2}"
          let r := ← combine res1 res2
          return r.1
        | _ => throwError "Found no model with corners on {src}"
    let some (srcJ, normedSpacesOnlyJ) := ← findModelInner tgt baseInfo
      | match_expr tgt with
        | Prod tgt1 tgt2 =>
          trace[Elab.DiffGeo.MDiff] "Expression {tgt} is a product, recursing into each factor"
          let some res1 := ← findModelInner tgt1 baseInfo
            | throwError "Found no model with corners on {tgt1}"
          let some res2 := ← findModelInner tgt2 baseInfo
            | throwError "Found no model with corners on {tgt2}"
          let r := ← combine res1 res2
          return r.1
        | _ => throwError "Found no model with corners on {tgt}"

    let r := combine (srcI, normedSpacesOnlyI) (srcJ, normedSpacesOnlyJ)
    return (← r).1
  | _ => throwError "Could not find a model with corners for {e}"
where
  /- Form the product expression for two models with corners.
  -- Emits the wrong choice for the product of normed spaces, but at least warns about this. -/
  combine (eI eJ : Expr × Bool) : TermElabM (Expr × Bool) := do
    let aT : Term ← Term.exprToSyntax eI.1
    let bT : Term ← Term.exprToSyntax eJ.1
    let iTerm : Term ← ``(ModelWithCorners.prod $aT $bT)
    if eI.2 && eJ.2 then
      -- TODO: extract the respective expressions E and F (and their base fields),
      -- ensure the base fields coincide, and return the model over E × F instead.
      trace[Elab.DiffGeo.MDiff] "Product of normed spaces: computing the 'wrong' model!"
      return (← Term.elabTerm iTerm none, true)
    else
      return (← Term.elabTerm iTerm none, false)


/-- If the type of `e` is a non-dependent function between spaces `src` and `tgt`, try to find a
model with corners on both `src` and `tgt`. If successful, return both models.

We pass `e` instead of just its type for better diagnostics.

If `es` is `some`, we verify that `src` and the type of `es` are definitionally equal. -/
def findModels (e : Expr) (es : Option Expr) : TermElabM (Expr × Expr) := do
  let etype ← whnf <|← instantiateMVars <|← inferType e
  match etype with
  | .forallE _ src tgt _ =>
    if tgt.hasLooseBVars then
      -- TODO: try `T%` here, and if it works, add an interactive suggestion to use it
      throwError "Term {e} is a dependent function, of type {etype}\nHint: you can use the `T%` \
        elaborator to convert a dependent function to a non-dependent one"
    let srcI ← findModel src
    if let some es := es then
      let estype ← inferType es
      /- Note: we use `isDefEq` here since persistent metavariable assignments in `src` and
      `estype` are acceptable.
      TODO: consider attempting to coerce `es` to a `Set`. -/
      if !(← isDefEq estype <|← mkAppM ``Set #[src]) then
        throwError "The domain {src} of {e} is not definitionally equal to the carrier type of \
          the set {es} : {estype}"
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
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``MDifferentiableWithinAt #[srcI, tgtI, ef, es]

/-- `MDiffAt f x` elaborates to `MDifferentiableAt I J f x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
scoped elab:max "MDiffAt" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <|← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``MDifferentiableAt #[srcI, tgtI, e]

-- An alternate implementation for `MDiffAt`.
-- /-- `MDiffAt2 f x` elaborates to `MDifferentiableAt I J f x`,
-- trying to determine `I` and `J` from the local context.
-- The argument `x` can be omitted. -/
-- scoped elab:max "MDiffAt2" ppSpace t:term:arg : term => do
--   let e ← Term.elabTerm t none
--   let etype ← whnfR <|← instantiateMVars <|← inferType e
--   forallBoundedTelescope etype (some 1) fun src tgt ↦ do
--     if let some src := src[0]? then
--       let srcI ← findModel (← inferType src)
--       if Lean.Expr.occurs src tgt then
--         throwErrorAt t "Term {e} is a dependent function, of type {etype}\n\
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
  let et ← ensureIsFunction <|← Term.elabTerm t none
  let (srcI, tgtI) ← findModels et es
  mkAppM ``MDifferentiableOn #[srcI, tgtI, et, es]

/-- `MDiff f` elaborates to `MDifferentiable I J f`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "MDiff" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <|← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``MDifferentiable #[srcI, tgtI, e]

-- We ensure the type of `n` before checking `f` is a function to provide better error messages
-- in case e.g. just `n` was forgotten.

/-- `CMDiffAt[s] n f x` elaborates to `ContMDiffWithinAt I J n f s x`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
scoped elab:max "CMDiffAt[" s:term "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``ContMDiffWithinAt #[srcI, tgtI, ne, ef, es]

/-- `CMDiffAt n f x` elaborates to `ContMDiffAt I J n f x`
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
scoped elab:max "CMDiffAt" ppSpace nt:term:arg ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <|← Term.elabTerm t none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let (srcI, tgtI) ← findModels e none
  mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]

/-- `CMDiff[s] n f` elaborates to `ContMDiffOn I J n f s`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
scoped elab:max "CMDiff[" s:term "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let ef ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels ef es
  mkAppM ``ContMDiffOn #[srcI, tgtI, ne, ef, es]

/-- `CMDiff n f` elaborates to `ContMDiff I J n f`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
scoped elab:max "CMDiff" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let ne ← Term.elabTermEnsuringType nt q(WithTop ℕ∞)
  let e ← ensureIsFunction <|← Term.elabTerm f none
  let (srcI, tgtI) ← findModels e none
  mkAppM ``ContMDiff #[srcI, tgtI, ne, e]

/-- `mfderiv[u] f x` elaborates to `mfderivWithin I J f u x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "mfderiv[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← ensureIsFunction <|← Term.elabTerm t none
  let (srcI, tgtI) ← findModels e es
  mkAppM ``mfderivWithin #[srcI, tgtI, e, es]

/-- `mfderiv% f x` elaborates to `mfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "mfderiv%" ppSpace t:term:arg : term => do
  let e ← ensureIsFunction <|← Term.elabTerm t none
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
