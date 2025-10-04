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
- `MDiffAt[u] f x` for `MDifferentiableWithinAt I J f u x`
- `CMDiff n f` for `ContMDiff I J n f`
- `CMDiffAt n f x` for `ContMDiffAt I J n f x`
- `CMDiff[u] n f` for `ContMDiffOn I J n f u`
- `CMDiffAt[u] n f x` for `ContMDiffWithinAt I J n f u x`,
- `mfderiv[u] f x` for `mfderivWithin I J f u x`,
- `mfderiv% f x` for `mfderiv I J f x`.

In each of these cases, the models with corners are inferred from the domain and codomain of `f`.
The search for models with corners uses the local context and is (almost) only syntactic, hence
hopefully fast enough to always run.

This has no dedicated support for product manifolds (or product vector spaces) yet;
adding this is left for future changes. (It would need to make a choice between e.g. the
trivial model with corners on a product `E × F` and the product of the trivial models on `E` and
`F`). In these settings, the elaborators should be avoided (for now).

Secondly, this file adds an elaborator to ease working with sections in a fibre bundle,
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
- extend the elaborators to guess models with corners on product manifolds
  (this has to make a guess, hence cannot always be correct: but it could make the guess that
  is correct 90% of the time)
  For products of vector spaces `E × F`, this could print a warning about making a choice between
  the model in `E × F` and the product of the models on `E` and `F`.
- extend the elaborators to support `PartialHomeomorph`s and `PartialEquiv`s

- better error messages (as needed)
- further testing and fixing of edge cases
- add tests for all of the above
- add delaborators for these elaborators

-/

open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic
open Mathlib.Tactic

/-- Try to infer the universe of an expression `e` -/
def _root_.Lean.Expr.getUniverse (e : Expr) : TermElabM (Level) := do
    if let .sort (.succ u) ← instantiateMVars <|← inferType e then
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
elab:max "T% " t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← whnf <|← instantiateMVars <|← inferType e
  match etype with
  | .forallE x base (mkApp3 (.const ``Bundle.Trivial _) E E' _) _ =>
    trace[TotalSpaceMk] "Section of a trivial bundle"
    if ← withReducible (isDefEq E base) then
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
      let decltype ← instantiateMVars <|← inferType decl
      match decltype with
      | mkApp7 (.const `FiberBundle _) _ F _ _ E _ _ =>
        if ← withReducible (isDefEq E V) then
          return ← withLocalDecl x BinderInfo.default base fun x ↦ do
            let body ← mkAppM ``Bundle.TotalSpace.mk' #[F, x, .app e x]
            mkLambdaFVars #[x] body
      | _ => pure ()
  | .forallE x src tgt _ =>
    trace[TotalSpaceMk] "Section of a trivial bundle as a non-dependent function"
    let us ← src.getUniverse
    let ut ← tgt.getUniverse
    -- TODO: can `tgt` depend on `x` in a way that is not a function application?
    -- Check that `x` is not a bound variable in `tgt`!
    -- xxx: is this check fine or overzealous?
    if Lean.Expr.hasLooseBVars tgt then
      throwError m!"Term {tgt} has loose bound variables¬
      Hint: applying the 'T%' elaborator twice makes no sense."
    let trivBundle := mkAppN (.const `Bundle.Trivial [us, ut]) #[src, tgt]
    return ← withLocalDecl x BinderInfo.default src fun x ↦ do
      let body := mkAppN (.const ``Bundle.TotalSpace.mk' [us, ut, ut])
        #[src, trivBundle, tgt, x, .app e x]
      mkLambdaFVars #[x] body
  | _ => pure ()
  return e

/-- Try to find a `ModelWithCorners` instance on a type (represented by an expression `e`),
using the local context to infer the expected type. This supports the following cases:
- the model with corners on the total space of a vector bundle
- a model with corners on a manifold
- the trivial model `𝓘(𝕜, E)` on a normed space
- if the above are not found, try to find a `NontriviallyNormedField` instance on the type of `e`,
  and if successful, return `𝓘(𝕜)`.

Further cases can be added as necessary.

Return an expression describing the found model with corners.

`baseInfo` is only used for the first case, a model with corners on the total space of the vector
bundle. In this case, it contains a pair of expressions `(e, i)` describing the type of the base
and the model with corners on the base: these are required to construct the right model with
corners.

This implementation is not maximally robust yet.
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
          let decltype ← instantiateMVars <|← inferType decl
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
      let decltype ← instantiateMVars <|← inferType decl
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
        let decltype ← instantiateMVars <|← inferType decl
        match decltype with
        | mkApp7 (.const ``ModelWithCorners  _) _ _ _ _ _ H' _ =>
          if H' == H then
            trace[MDiffElab] m!"Found model: {decl}"
            return decl
        | _ => pure ()
    else
      trace[MDiffElab] m!"Hoping {e} is a normed field"
      let eT : Term ← PrettyPrinter.delab e
      let iTerm : Term ← `(𝓘($eT, $eT))
      let I ← Term.elabTerm iTerm none
      trace[MDiffElab] m!"Found model: {I}"
      return I
    throwError "Couldn’t find models with corners"

/-- If `etype` is a non-dependent function between spaces `src` and `tgt`, try to find a model with
corners on both `src` and `tgt`. If successful, return both models.

`ef` is the term having type `etype`: this is used only for better diagnostics.
If `estype` is `some`, we verify that `src` and `estype` are def-eq. -/
def _find_models (etype eterm : Expr) (estype : Option Expr) :
    TermElabM (Option (Expr × Expr)) := do
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    if Lean.Expr.hasLooseBVars tgt then
      throwError m!"Term {eterm} is a dependent function, of type {etype}\n\
      Hint: you can use the 'T%' elaborator to convert a dependent function to a non-dependent one"
    if let some es := estype then
      if !(← isDefEq es (← mkAppM ``Set #[src])) then
        throwError m!"The domain {src} of {eterm} is not definitionally equal to the carrier
        of the type {es} of the set 's' passed in"
    let tgtI ← find_model tgt (src, srcI)
    return some (srcI, tgtI)
  | _ => return none

/-- `MDiffAt[s] f x` elaborates to `MDifferentiableWithinAt I J f s x`,
trying to determine `I` and `J` from the local context.
The argument x can be omitted. -/
elab:max "MDiffAt[" s:term:arg "]" ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let etype ← instantiateMVars <|← inferType ef
  let estype ← instantiateMVars <|← inferType es
  match ← _find_models etype ef estype with
  | some (srcI, tgtI) => return ← mkAppM ``MDifferentiableWithinAt #[srcI, tgtI, ef, es]
  | none => throwError m!"Term {ef} is not a function."

/-- `MDiffAt f x` elaborates to `MDifferentiableAt I J f x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
elab:max "MDiffAt" ppSpace t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← instantiateMVars <|← inferType e
  match ← _find_models etype e none with
  | some (srcI, tgtI) => return ← mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
  | none => throwError m!"Term {e} is not a function."

-- This implement is more robust (in theory), but currently fails tests.
-- TODO: investigate why, fix this and replace `MDiffAt` by this one!
/-- `MDiffAt2 f x` elaborates to `MDifferentiableAt I J f x`,
trying to determine `I` and `J` from the local context.
The argument `x` can be omitted. -/
elab:max "MDiffAt2" ppSpace t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← instantiateMVars <|← inferType e
  forallBoundedTelescope etype (some 1) fun src tgt ↦ do
    if let some src := src[0]? then
      let srcI ← find_model src
      if Lean.Expr.occurs src tgt then
        throwError m!"Term {e} is a dependent function, of type {etype}\n\
        Hint: you can use the 'T%' elaborator to convert a dependent function \
        to a non-dependent one"
      let tgtI ← find_model tgt (src, srcI)
      return ← mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
    else
      throwError m!"Term {e} is not a function."

/-- `MDiff[s] f` elaborates to `MDifferentiableOn I J f s`,
trying to determine `I` and `J` from the local context. -/
elab:max "MDiff[" s:term:arg "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let et ← Term.elabTerm t none
  let estype ← instantiateMVars <|← inferType es
  let etype ← instantiateMVars <|← inferType et
  match ← _find_models etype et estype with
  | some (srcI, tgtI) => return ← mkAppM ``MDifferentiableOn #[srcI, tgtI, et, es]
  | none => throwError m!"Term {et} is not a function."

/-- `MDiff f` elaborates to `MDifferentiable I J f`,
trying to determine `I` and `J` from the local context. -/
elab:max "MDiff" ppSpace t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← instantiateMVars <|← inferType e
  match ← _find_models etype e none with
  | some (srcI, tgtI) => return ← mkAppM ``MDifferentiable #[srcI, tgtI, e]
  | none => throwError m!"Term {e} is not a function."

/-- `CMDiffAt[s] n f x` elaborates to `ContMDiffWithinAt I J n f s x`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
elab:max "CMDiffAt[" s:term:arg "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let estype ← instantiateMVars <|← inferType es
  let eftype ← instantiateMVars <|← inferType ef
  match ← _find_models eftype ef estype with
  | some (srcI, tgtI) => return ← mkAppM ``ContMDiffWithinAt #[srcI, tgtI, ne, ef, es]
  | none => throwError m!"Term {ef} is not a function."

/-- `CMDiffAt n f x` elaborates to `ContMDiffAt I J n f x`
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported).
The argument `x` can be omitted. -/
elab:max "CMDiffAt" ppSpace nt:term:arg ppSpace t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← ``(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let etype ← instantiateMVars <|← inferType e
  match ← _find_models etype e none with
  | some (srcI, tgtI) => return ← mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]
  | none => throwError m!"Term {e} is not a function."

/-- `CMDiff[s] n f` elaborates to `ContMDiffOn I J n f s`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
elab:max "CMDiff[" s:term:arg "]" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let es ← Term.elabTerm s none
  let ef ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← ``(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let estype ← instantiateMVars <|← inferType es
  let eftype ← instantiateMVars <|← inferType ef
  match ← _find_models eftype ef estype with
  | some (srcI, tgtI) => return ← mkAppM ``ContMDiffOn #[srcI, tgtI, ne, ef, es]
  | none => throwError m!"Term {ef} is not a function."

/-- `CMDiff n f` elaborates to `ContMDiff I J n f`,
trying to determine `I` and `J` from the local context.
`n` is coerced to `WithTop ℕ∞` if necessary (so passing a `ℕ`, `∞` or `ω` are all supported). -/
elab:max "CMDiff" ppSpace nt:term:arg ppSpace f:term:arg : term => do
  let e ← Term.elabTerm f none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let etype ← instantiateMVars <|← inferType e
  match ← _find_models etype e none with
  | some (srcI, tgtI) => return ← mkAppM ``ContMDiff #[srcI, tgtI, ne, e]
  | none => throwError m!"Term {e} is not a function."

/-- `mfderiv[u] f x` elaborates to `mfderivWithin I J f u x`,
trying to determine `I` and `J` from the local context. -/
elab:max "mfderiv[" s:term:arg "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
  let e ← Term.elabTerm t none
  let etype ← instantiateMVars <|← inferType e
  let estype ← instantiateMVars <|← inferType es
  match ← _find_models etype e estype with
  | some (srcI, tgtI) => return ← mkAppM ``mfderivWithin #[srcI, tgtI, e, es]
  | none => throwError m!"Term {e} is not a function."

/-- `mfderiv% f x` elaborates to `mfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
elab:max "mfderiv%" ppSpace t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← instantiateMVars <|← inferType e
  match ← _find_models etype e none with
  | some (srcI, tgtI) => return ← mkAppM ``mfderiv #[srcI, tgtI, e]
  | none => throwError m!"Term {e} is not a function."

end Manifold
