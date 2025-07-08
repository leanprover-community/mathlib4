/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.Traces

/-!
# Elaborators for differential geometry

TODO: add a more complete doc-string

-/

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

open Lean Meta Elab Tactic
open Mathlib.Tactic

def _root_.Lean.Expr.getUniverse (e : Expr) : TermElabM (Level) := do
    if let .sort (.succ u) ← inferType e >>= instantiateMVars then
      return u
    else
      throwError m!"Could not find universe of {e}."

@[match_pattern] def mkApp12 (f a b c d e g e₁ e₂ e₃ e₄ e₅ e₆ : Expr) :=
  mkApp6 (mkApp6 f a b c d e g) e₁ e₂ e₃ e₄ e₅ e₆

elab "T%" t:term : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE x base (mkApp3 (.const `Bundle.Trivial _) E E' _) _ =>
    trace[TotalSpaceMk] "Section of a trivial bundle"
    if E == base then
      return ← withLocalDecl x BinderInfo.default base fun x ↦ do
        let body ← mkAppM ``Bundle.TotalSpace.mk' #[E', x, .app e x]
        mkLambdaFVars #[x] body
  | .forallE x base (mkApp12 (.const `TangentSpace _) _k _ E _ _ _H _ _I _M _ _ _x) _ =>
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

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}

/-- info: fun x ↦ TotalSpace.mk' F x (σ x) : M → TotalSpace F V -/
#guard_msgs in
#check T% σ

/-- info: fun x ↦ TotalSpace.mk' E' x (σ' x) : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% σ'

/-- info: fun a ↦ TotalSpace.mk' E' a (s a) : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% s

variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-- info: fun m ↦ TotalSpace.mk' E m (X m) : M → TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check T% X

example : (fun m ↦ (X m : TangentBundle I M)) = (fun m ↦ TotalSpace.mk' E m (X m)) := rfl

-- FIXME: better failure when trying to find a normedfield instance
def find_model (e : Expr) (baseInfo : Option (Expr × Expr) := none) : TermElabM Expr := do
    trace[MDiffElab] m!"Searching a model for: {e}"
    if let mkApp3 (.const `Bundle.TotalSpace _) _ F V := e then
      if let mkApp12 (.const `TangentSpace _) _k _ _E _ _ _H _ I M _ _ _x := V then
        trace[MDiffElab] m!"This is the total space of the tangent bundle of {M}"
        let srcIT : Term ← PrettyPrinter.delab I
        let resTerm : Term ← `(ModelWithCorners.prod $srcIT ModelWithCorners.tangent $srcIT)
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
          | mkApp4 (.const `NormedSpace _) K' E _ _ =>
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
        let iTerm : Term ← `(ModelWithCorners.prod $srcIT 𝓘($kT, $FT))
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
      | mkApp4 (.const `ChartedSpace _) H' _ M _ =>
        if M == e then
          H := H'
          trace[MDiffElab] m!"H is: {H}"
          Hok := true
      | mkApp4 (.const `NormedSpace _) K' E _ _ =>
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
      let iTerm : Term ← `(𝓘($eK, $eT))
      let I ← Term.elabTerm iTerm none
      trace[MDiffElab] m!"Found model: {I}"
      return I
      -- let uK ← K.getUniverse
      -- let normedFieldK ← synthInstance (.app (.const `NontriviallyNormedField [uK]) K)
      -- trace[MDiffElab] m!"NontriviallyNormedField instance is: {normedFieldK}"
      -- let ue ← e.getUniverse
      -- let normedGroupE ← synthInstance (.app (.const `NormedAddCommGroup  [ue]) e)
      -- trace[MDiffElab] m!"NormedAddCommGroup  instance is: {normedGroupE}"
      -- return mkAppN (.const `modelWithCornersSelf [uK, ue])
      --   #[K, normedFieldK, e, normedGroupE, normedSpaceInst]
    else if Hok then
      for decl in ← getLocalHyps do
        let decltype ← inferType decl >>= instantiateMVars
        match decltype with
        | mkApp7 (.const `ModelWithCorners  _) _ _ _ _ _ H' _ =>
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

-- TODO: scope all these elaborators to the `Manifold` namespace

-- `MDiffAt[s] f x` elaborates to `MDifferentiableWithinAt I J f s x`,
-- trying to determine `I` and `J` from the local context.
-- The argument x can be omitted.
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

-- `MDiffAt f x` elaborates to `MDifferentiableAt I J f x`,
-- trying to determine `I` and `J` from the local context.
elab:max "MDiffAt" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

-- FIXME: remove in favour of MDiffAt (once that one is scoped)
elab:max "MDifferentiableAt%" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiableAt #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

-- `MDiff[s] f` elaborates to `MDifferentiableOn I J f`, trying to determine `I` and `J` from the
-- local context.
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

-- `MDiff f` elaborates to `MDifferentiable I J f`,
-- trying to determine `I` and `J` from the local context.
elab:max "MDiff" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiable #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

-- TODO: remove in favour of MDiff
elab:max "MDifferentiable%" t:term:arg : term => do
  let e ← Term.elabTerm t none
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``MDifferentiable #[srcI, tgtI, e]
  | _ => throwError m!"Term {e} is not a function."

-- `CMDiffAt[s] n f` elaborates to `ContMDiffWithinAt I J n f s`
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

-- `CMDiffAt n f` elaborates to `ContMDiffAt I J n f s`
elab:max "CMDiffAt" nt:term:arg t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTerm nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

-- `CMDiff[s] n f` elaborates to `ContMDiffOn I J n f s`
elab:max "CMDiff[" s:term:arg "]" nt:term:arg f:term:arg : term => do
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
    return ← mkAppM ``ContMDiffOn #[srcI, tgtI, ne, ef, es]
  | _ => throwError m!"Term {ef} is not a function."

-- `CMDiff n f` elaborates to `ContMDiff I J n f`
elab:max "CMDiff" nt:term:arg t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTerm nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiff #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

-- TODO: remove in favour of CMDiff
elab:max "ContMDiff%" nt:term:arg t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiff #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

-- TODO: remove in favour of CMDiffAt
elab:max "ContMDiffAt%" nt:term:arg t:term:arg : term => do
  let e ← Term.elabTerm t none
  let wtn ← Term.elabTerm (← `(WithTop ℕ∞)) none
  let ne ← Term.elabTermEnsuringType nt wtn
  let etype ← inferType e >>= instantiateMVars
  match etype with
  | .forallE _ src tgt _ =>
    let srcI ← find_model src
    let tgtI ← find_model tgt (src, srcI)
    return ← mkAppM ``ContMDiffAt #[srcI, tgtI, ne, e]
  | _ => throwError m!"Term {e} is not a function."

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  (f : M → M') (m : M)

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) fun m ↦ TotalSpace.mk' E m (X m) : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% X)

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m)) m : Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% X) m

/-- info: ContMDiff I (I.prod 𝓘(𝕜, E)) 1 fun m ↦ TotalSpace.mk' E m (X m) : Prop -/
#guard_msgs in
#check ContMDiff% 1 (T% X)

/-- info: ContMDiffAt I (I.prod 𝓘(𝕜, E)) 1 (fun m ↦ TotalSpace.mk' E m (X m)) m : Prop -/
#guard_msgs in
#check ContMDiffAt% 1 (T% X) m

/-- info: MDifferentiableAt I I' f : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% f

/-- info: MDifferentiableAt I I' f m : Prop -/
#guard_msgs in
#check MDifferentiableAt% f m

variable (g : E → E')
-- set_option trace.MDiffElab true in

/-- info: MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') g : E → Prop -/
#guard_msgs in
#check MDifferentiableAt% g

variable (h : 𝕜 → E')

/-- info: MDifferentiableAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, E') h : 𝕜 → Prop -/
#guard_msgs in
#check MDifferentiableAt% h

variable (h' : M → 𝕜)

/-- info: MDifferentiableAt I 𝓘(𝕜, 𝕜) h' : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% h'

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, F)) fun x ↦ TotalSpace.mk' F x (σ x) : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% σ)

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun x ↦ TotalSpace.mk' E' x (σ' x) : E → Prop
-/
#guard_msgs in
#check MDifferentiableAt% (T% σ')

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun a ↦ TotalSpace.mk' E' a (s a) : E → Prop
-/
#guard_msgs in
#check MDifferentiableAt% (T% s)

end
