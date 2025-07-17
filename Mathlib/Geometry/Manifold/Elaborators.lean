/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Traces

/-!
# Elaborators for differential geometry

This file defines custom elaborators for differential geometry, to allow for more compact notation.
There are two classes of elaborators. The first provides more compact notation for differentiability
and continuous differentiability on manifolds, including inference of the model with corners.
All these elaborators are scoped to the `Manifold` namespace. They allow writing
- `MDiff f` for `MDifferentiable I J f`
- `MDiffAt f x` for `MDifferentiableAt I J f x`
- `MDiff[u] f` for `MDifferentiableOn I J f u`
- `MDiffAt[u] f` for `DifferentiableWithinAt I J f u x`
- `CMDiff n f` for `ContMDiff I J n f`
- `CMDiffAt n f x` for `ContMDiffAt I J n f x`
- `CMDiff[u] n f` for `ContMDiffOn I J n f u`
- `CMDiffAt[u] n f` for `ContMDiffWithinAt I J n f u x`,
- `mfderiv[u] f x` for `mfderivWithin I J f s x`,
- `mfderiv% f x` for `mfderiv I J f x`.

In each of these cases, the models with corners are inferred from the domain and codomain of `f`.
The search for models with corners uses the local context and is (almost) only syntactic, hence
hopefully fast enough to always run.

Secondly, this space adds an elaborator to ease working with sections in a fibre bundle,
converting a section `s : Π x : M, Π V x` to a non-dependent function into the total space of the
bundle.
```lean
-- omitted: let `V` be a fibre bundle over `M`
variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}

-- outputs `fun x ↦ TotalSpace.mk' F x (σ x) : M → TotalSpace F V`
#check T% σ

-- outputs `fun x ↦ TotalSpace.mk' E' x (σ' x) : E → TotalSpace E' (Trivial E E')`
-- Note how the name of the bound variable `x` is preserved.
#check T% σ'

-- outputs `fun a ↦ TotalSpace.mk' E' a (s a) : E → TotalSpace E' (Trivial E E')`
#check T% s
```

These elaborators can be combined: `CMDiffAt[u] n (T% s) x`

**Warning.** These elaborators are a proof of concept; the implementation should be considered a
prototype. Don't rewrite all of mathlib to use it just yet. Notable bugs and limitations include
the following.

## TODO
- extend the feature to infer e.g. models with corners on product manifolds
  (this has to make a guess, hence cannot always be correct: but it could make the guess that
  is correct 90% of the time)
- fix pretty-printing: currently, the `commandStart` linter expects some different formatting
- better error messages: forgetting e.g. the `T%` elaborator yields cryptic errors
- further testing and fixing of edge cases
- add test for the difference between `CMDiff` and `ContMDiff%` (and decide on one behaviour)
- added tests for all of the above

-/

open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic
open Mathlib.Tactic

/-- Try to infer the universe of an expression `e` -/
def _root_.Lean.Expr.getUniverse (e : Expr) : TermElabM (Level) := do
    if let .sort (.succ u) ← inferType e >>= instantiateMVars then
      return u
    else
      throwError m!"Could not find universe of {e}."

/-- Call `mkApp` recursively with 12 arguments -/
@[match_pattern] def mkApp12 (f a b c d e g e₁ e₂ e₃ e₄ e₅ e₆ : Expr) :=
  mkApp6 (mkApp6 f a b c d e g) e₁ e₂ e₃ e₄ e₅ e₆

namespace Manifold

/-- Elaborator for sections in a fibre bundle: converts a section as a dependent function
to a non-dependent function into the total space. This handles the cases of
- sections of a trivial bundle
- vector fields on a manifold (i.e., sections of the tangent bundle)
- sections of an explicit fibre bundle
- turning a bare function `E → E'` into a section of the trivial bundle `Bundle.Trivial E E'`

This elaborator operates purely syntactically, by analysing the local contexts for suitable
hypothesis for the above cases. Therefore, it is (hopefully) fast enough to always run.
-/
-- TODO: document how this elaborator works, any gotchas, etc.
elab "T% " t:term : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE x base (mkApp3 (.const ``Bundle.Trivial _) E E' _) _ =>
    trace[TotalSpaceMk] "Section of a trivial bundle"
    if E == base then
      return ← withLocalDecl x BinderInfo.default base fun x ↦ do
        let body ← mkAppM ``Bundle.TotalSpace.mk' #[E', x, .app e x]
        mkLambdaFVars #[x] body
  | .forallE x base (mkApp12 (.const ``TangentSpace _) _k _ E _ _ _H _ _I _M _ _ _x) _ =>
    trace[TotalSpaceMk] "Vector field"
    return ← withLocalDecl x BinderInfo.default base fun x ↦ do
      let body ← mkAppM ``Bundle.TotalSpace.mk' #[E, x, .app e x]
      mkLambdaFVars #[x] body
  | .forallE x base (.app V _) _ =>
    trace[TotalSpaceMk] "Section of a bundle as a dependent function"
    for decl in ← getLocalHyps do
      let decltype ← inferType decl >>= instantiateMVars
      match decltype with
      | mkApp7 (.const `FiberBundle _) _ F _ _ E _ _ =>
        if E == V then
          return ← withLocalDecl x BinderInfo.default base fun x ↦ do
            let body ← mkAppM ``Bundle.TotalSpace.mk' #[F, x, .app e x]
            mkLambdaFVars #[x] body
      | _ => pure ()
  | .forallE x src tgt _ =>
    trace[TotalSpaceMk] "Section of a trivial bundle as a non-dependent function"
    let us ← src.getUniverse
    let ut ← tgt.getUniverse
    let triv_bundle := mkAppN (.const `Bundle.Trivial [us, ut]) #[src, tgt]
    return ← withLocalDecl x BinderInfo.default src fun x ↦ do
      let body := mkAppN (.const ``Bundle.TotalSpace.mk' [us, ut, ut])
        #[src, triv_bundle, tgt, x, .app e x]
      mkLambdaFVars #[x] body
  | _ => pure ()
  return e

/-- Try to find a `ModelWithCorners` instance on an expression `e`, using the local context
to infer the expected type. This supports the following cases:
- the model with corners on the total space of a vector bundle
- a model with corners on a manifold
- the trivial model `𝓘(𝕜, E)` on a normed space
- if the above are not found, try to find a `NontriviallyNormedField` instance on the type of `e`,
  and if successful, return `𝓘(𝕜)`.

Further cases can be added as necessary.
This implementation is not maximally robust yet, but already useful.
-/
-- FIXME: better failure when trying to find a `NormedField` instance
def find_model (e : Expr) (baseInfo : Option (Expr × Expr) := none) : TermElabM Expr := do
    trace[MDiffElab] m!"Searching a model for: {e}"
    if let mkApp3 (.const ``Bundle.TotalSpace _) _ F V := e then
      if let mkApp12 (.const ``TangentSpace _) _k _ _E _ _ _H _ I M _ _ _x := V then
        trace[MDiffElab] m!"This is the total space of the tangent bundle of {M}"
        let srcIT : Term ← PrettyPrinter.delab I
        let resTerm : Term ← ``(ModelWithCorners.prod $srcIT ModelWithCorners.tangent $srcIT)
        let res ← Term.elabTerm resTerm none
        trace[MDiffElab] m!"Found model: {res}"
        return res

      trace[MDiffElab] m!"This is a total space with fiber {F}"
      if let some (_src, srcI) := baseInfo then
        let mut K : Expr := default
        let mut normedSpaceInst : Expr := default
        let mut Kok : Bool := false
        for decl in ← getLocalHyps do
          let decltype ← inferType decl >>= instantiateMVars
          match decltype with
          | mkApp4 (.const ``NormedSpace _) K' E _ _ =>
            if E == F then
              K := K'
              trace[MDiffElab] m!"{F} is a normed field over {K}"
              normedSpaceInst := decl
              Kok := true
          | _ => pure ()
          if Kok then break
        unless Kok do throwError
          m!"Couldn’t find a normed space structure on {F} in local context"
        let kT : Term ← PrettyPrinter.delab K
        let srcIT : Term ← PrettyPrinter.delab srcI
        let FT : Term ← PrettyPrinter.delab F
        let iTerm : Term ← ``(ModelWithCorners.prod $srcIT 𝓘($kT, $FT))
        let I ← Term.elabTerm iTerm none
        trace[MDiffElab] m!"Found model: {I}"
        return I

      else
        throwError "Having a TotalSpace as source is not yet supported"
    let mut H : Expr := default
    let mut Hok : Bool := false
    let mut K : Expr := default
    let mut normedSpaceInst : Expr := default
    let mut Kok : Bool := false
    for decl in ← getLocalHyps do
      let decltype ← inferType decl >>= instantiateMVars
      match decltype with
      | mkApp4 (.const ``ChartedSpace _) H' _ M _ =>
        if M == e then
          H := H'
          trace[MDiffElab] m!"H is: {H}"
          Hok := true
      | mkApp4 (.const ``NormedSpace _) K' E _ _ =>
        if E == e then
          K := K'
          trace[MDiffElab] m!"Field is: {K}"
          normedSpaceInst := decl
          Kok := true
      | _ => pure ()
      if Hok || Kok then break
    if Kok then
      let eT : Term ← PrettyPrinter.delab e
      let eK : Term ← PrettyPrinter.delab K
      let iTerm : Term ← ``(𝓘($eK, $eT))
      let I ← Term.elabTerm iTerm none
      trace[MDiffElab] m!"Found model: {I}"
      return I
      -- let uK ← K.getUniverse
      -- let normedFieldK ← synthInstance (.app (.const ``NontriviallyNormedField [uK]) K)
      -- trace[MDiffElab] m!"NontriviallyNormedField instance is: {normedFieldK}"
      -- let ue ← e.getUniverse
      -- let normedGroupE ← synthInstance (.app (.const ``NormedAddCommGroup  [ue]) e)
      -- trace[MDiffElab] m!"NormedAddCommGroup  instance is: {normedGroupE}"
      -- return mkAppN (.const `modelWithCornersSelf [uK, ue])
      --   #[K, normedFieldK, e, normedGroupE, normedSpaceInst]
    else if Hok then
      for decl in ← getLocalHyps do
        let decltype ← inferType decl >>= instantiateMVars
        match decltype with
        | mkApp7 (.const ``ModelWithCorners  _) _ _ _ _ _ H' _ =>
          if H' == H then
            trace[MDiffElab] m!"Found model: {decl}"
            return decl
        | _ => pure ()
      -- throwError m!"Couldn’t find models with corners with H = {H}"
    else
      trace[MDiffElab] m!"Hoping {e} is a normed field"
      let eT : Term ← PrettyPrinter.delab e
      let iTerm : Term ← `(𝓘($eT, $eT))
      let I ← Term.elabTerm iTerm none
      trace[MDiffElab] m!"Found model: {I}"
      return I

    throwError "Couldn’t find models with corners"

/-- `MDiffAt[s] f x` elaborates to `MDifferentiableWithinAt I J f s x`,
trying to determine `I` and `J` from the local context.
The argument x can be omitted. -/
elab:max "MDiffAt[" s:term:arg "]" f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let etype ← inferType ef >>= instantiateMVars
  let _estype ← inferType ef >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    -- TODO: check that `estype` and src are compatible/the same!
    return ← mkAppM ``MDifferentiableWithinAt #[srcI, tgtI, ef, es]
  | _ => throwError m!"Term {ef} is not a function."

/-- `MDiffAt f x` elaborates to `MDifferentiableAt I J f x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
elab:max "MDiffAt" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

/-- `MDiff[s] f` elaborates to `MDifferentiableOn I J f`,
trying to determine `I` and `J` from the local context. -/
elab:max "MDiff[" s:term:arg "]" t:term:arg : term => do
  let es ← Term.elabTerm s none
  let et ← Term.elabTerm t none
  let _estype ← inferType es >>= instantiateMVars
  let etype ← inferType et >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    -- TODO: check that `estype` and src are compatible/the same!
    return ← mkAppM ``MDifferentiableOn #[srcI, tgtI, et, es]
  | _ => throwError m!"Term {et} is not a function."

/-- `MDiff f` elaborates to `MDifferentiable I J f`,
trying to determine `I` and `J` from the local context. -/
elab:max "MDiff" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiable #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

-- TODO: say something about the expected type of `n` being in ℕ or WithTop ℕ∞!
/-- `CMDiffAt[s] n f x` elaborates to `ContMDiffWithinAt I J n f s x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
elab:max "CMDiffAt[" s:term:arg "]" nt:term:arg f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTerm nt wtn
  let _estype ← inferType es >>= instantiateMVars
  let eftype ← inferType ef >>= instantiateMVars
  match eftype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    -- TODO: check `estype` and src are compatible
    return ← mkAppM ``ContMDiffWithinAt #[srcI, tgtI, ne, ef, es]
  | _ => throwError m!"Term {ef} is not a function."

/-- `CMDiffAt n f x` elaborates to `ContMDiffAt I J n f x`
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
elab:max "CMDiffAt" nt:term:arg t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← ``(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

/-- `CMDiff[s] n f` elaborates to `ContMDiffOn I J n f s`,
trying to determine `I` and `J` from the local context. -/
elab:max "CMDiff[" s:term:arg "]" nt:term:arg f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← ``(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let _estype ← inferType es >>= instantiateMVars
  let eftype ← inferType ef >>= instantiateMVars
  match eftype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    -- TODO: check `estype` and src are compatible
    return ← mkAppM ``ContMDiffOn #[srcI, tgtI, ne, ef, es]
  | _ => throwError m!"Term {ef} is not a function."

/-- `CMDiff n f` elaborates to `ContMDiff I J n f`,
trying to determine `I` and `J` from the local context. -/
elab:max "CMDiff" nt:term:arg f:term:arg : term => do
  let e ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTerm nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiff #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

/-- `mfderiv[u] f x` elaborates to `mfderivWithin I J f x`,
trying to determine `I` and `J` from the local context. -/
elab:max "mfderiv[" s:term:arg "]" t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  let _estype ← inferType es >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    -- TODO: check `estype` and src are compatible
    return ← mkAppM ``mfderivWithin #[srcI, tgtI, e, es]
  | _ => throwError m!"Term {e} is not a function."

/-- `mfderiv f x` elaborates to `mfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
elab:max "mfderiv%" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM `mfderiv #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

end Manifold
