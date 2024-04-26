/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Kyle Miller
-/
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.CollectFVars
import Lean.Meta.Tactic.Generalize
import Lean.Elab.Tactic.Location
import Mathlib.Lean.Expr.Basic

/-!
# The `generalize_proofs` tactic

Generalize any proofs occurring in the goal or in chosen hypotheses,
replacing them by local hypotheses.
When these hypotheses are named, this makes it easy to refer to these proofs later in a proof,
commonly useful when dealing with functions like `Classical.choose` that produce data from proofs.
It is also useful to eliminate proof terms to handle issues with dependent types.

For example:
```lean
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```
-/

namespace Mathlib.Tactic
open Lean Meta Elab Parser.Tactic Elab.Tactic

initialize registerTraceClass `Tactic.generalize_proofs

namespace GeneralizeProofs

/--
State for the generalize proofs tactic.
Contains the remaining names to be used and the list of generalizations so far.
-/
structure GState where
  /-- Source of names to use for generalized proofs,
  where `none` means to generate an inaccessible name. -/
  nextNames : List (Option Name)
  /-- Mapping from propositions to proofs, used to merge proofs.
  These should all be valid with respect to the original local context. -/
  propToProof : ExprMap Expr
  /-- The fvar/prop/proof triples to add to the local context. -/
  generalizations : Array (Name × Expr × Expr) := #[]

/--
Monad used to generalize proofs.
Carries a state (`Mathlib.Tactic.GeneralizeProofs.State`) keeping track of current generalizations.
-/
abbrev MGen := StateRefT GState MetaM

/-- Gets the next name from `State.nextNames`. Returns `none` if a name should be generated. -/
def nextName? : MGen (Option Name) := do
  let n? := (← get).nextNames.headD none
  modify fun s ↦ { s with nextNames := s.nextNames.tail }
  return n?

/--
Monad used to abstract proofs, to prepare for generalization.
Wraps the `MGen` monad and has a cache mapping expressions
to expressions that have had their proofs abstracted.
-/
abbrev MAbs := MonadCacheT Expr Expr <| MGen

/--
Abstract proofs occurring in the expression.
A proof is *abstracted* if it is of the form `f a b ...` where `a b ...` are bound variables
(that is, they are variables that are not present in the initial local context)
and where `f` contains no bound variables.
In this form, `f` can be immediately lifted to be a local variable and generalized.
The abstracted proofs are recorded in the state.

This function is careful to track the type of `e` based on where it's used,
since the inferred type might be different.
For example, `(by simp : 1 < [1, 2].length)` has `1 < Nat.succ 1` as the inferred type.
-/
partial def abstractProofs (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  visit (← instantiateMVars e) ty? #[] false
where
  /--
  Core implementation of `abstractProofs`.
  - `fvars` is the current list of bound variables.
  - `hasLet` is whether any of the `fvars` is a let variable, for an optimization in `visitProof`.
  -/
  visit (e : Expr) (ty? : Option Expr) (fvars : Array Expr) (hasLet : Bool) : MAbs Expr := do
    if e.isAtomic then
      return e
    else
      checkCache e fun _ ↦ do
        let ty ← ty?.getDM (inferType e)
        if ← isProof e then
          visitProof e ty fvars [] hasLet
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none fvars hasLet) fun x ↦ do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none (fvars.push x) hasLet)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none fvars hasLet) fun x ↦ do
              let ty ← whnfD ty
              if !ty.isForall then panic! "Expecting forall in abstractProofs .lam"
              let ty' := ty.instantiate1 x
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty' (fvars.push x) hasLet)
          | .letE n t v b _ =>
            let t' ← visit t none fvars hasLet
            withLetDecl n t' (← visit v t' fvars hasLet) fun x ↦ do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty (fvars.push x) true)
          | .app .. =>
            e.withApp fun f args ↦ do
              -- For simplicity, don't try to propagate the type into the function.
              let f' ← visit f none fvars hasLet
              let mut fty ← inferType f'
              let mut args' := #[]
              let mut unifiedTy := false
              for i in [0:args.size] do
                if args'.size ≤ i then
                  let (args'', _, fty') ← forallMetaBoundedTelescope fty (args.size - i)
                  if args''.isEmpty then panic! "Could not make progress in abstractProofs .app"
                  fty := fty'
                  args' := args' ++ args''
                if !unifiedTy && args'.size == args.size then
                  unifiedTy ← isDefEqGuarded fty ty
                let argTy := (← instantiateMVars <| ← inferType args'[i]!).cleanupAnnotations
                let arg' ← visit args[i]! argTy fvars hasLet
                unless ← isDefEq argTy (← inferType arg') do
                  panic! s!"failed isDefEq for .app {i}, {← ppExpr args'[i]!}, {← ppExpr args[i]!}"
                args'[i]!.mvarId!.assign arg'
              instantiateMVars <| mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty fvars hasLet)
          -- Giving up propagating expected types for `.proj`, which we shouldn't see anyway
          | .proj _ _ b => return e.updateProj! (← visit b none fvars hasLet)
          | _           => unreachable!
  /--
  Core implementation of abstracting a proof.
  The `ty` argument is the type of `mkAppN e appliedFVars`.
  -/
  visitProof (e ty : Expr) (fvars : Array Expr) (appliedFVars : List Expr) (hasLet : Bool) :
      MAbs Expr := do
    -- 0. eliminate mdata
    if let .mdata _ e' := e then
      return ← visitProof e' ty fvars appliedFVars hasLet
    -- 1. peel off fvars corresponding to bound variables.
    if let .app f x := e then
      if fvars.contains x then
        return ← visitProof f ty fvars (x :: appliedFVars) hasLet
    -- 2. zeta reduce to ensure that there are no dependencies on lets from `fvars`.
    let e ←
      if hasLet then
        Meta.transform (usedLetOnly := true) e fun node => do
          match node with
          | .fvar fvarId =>
            if fvars.contains node then
              if let some val ← fvarId.getValue? then
                return .visit val
            return .done node
          | _ => return .continue
      else
        pure e
    -- 3. if atomic, then no use in abstracting
    if e.isAtomic then
      trace[Tactic.generalize_proofs] "3 atomic"
      return appliedFVars.foldl .app e
    -- 4. abstract `fvars` out of `e` to make the abstracted proof `pf`
    let usedFVars := (collectFVars {} e).fvarSet
    let fvars' := fvars.filter (fun fvar => usedFVars.contains fvar.fvarId!)
    let pf ← mkLambdaFVars fvars' e
    -- this is a big approximation for type propagation:
    let pfTy ← if appliedFVars.isEmpty then pure ty else instantiateMVars (← inferType pf)
    -- 5. check if there is already a recorded proof for this proposition.
    trace[Tactic.generalize_proofs] "finding {pfTy}"
    if let some pf' := (← get).propToProof.find? pfTy then
      trace[Tactic.generalize_proofs] "5 found proof"
      return appliedFVars.foldl .app (mkAppN pf' fvars')
    -- 6. record the proof in the state and return the proof.
    let name ← (← nextName?).getDM (mkFreshUserName `h)
    modify fun s =>
      { s with
        propToProof := s.propToProof.insert pfTy pf
        generalizations := s.generalizations.push (name, pfTy, pf) }
    trace[Tactic.generalize_proofs] "6 added"
    return appliedFVars.foldl .app (mkAppN pf fvars')

/--
Create a mapping of all propositions in the local context to their fvars.
-/
def initialPropToProof : MetaM (ExprMap Expr) := do
  -- Visit decls in reverse order so that in case there are duplicates,
  -- earlier proofs are preferred
  (← getLCtx).foldrM (init := {}) fun decl m => do
    if !decl.isImplementationDetail then
      let ty := (← instantiateMVars decl.type).cleanupAnnotations
      if ← Meta.isProp ty then
        return m.insert ty decl.toExpr
    return m

/--
Generalizes the proofs in the type `e` and runs `k` in a local context with these propositions.
This continuation `k` is passed
1. an array of fvars for the propositions
2. an array of proof terms (extracted from `e`) that prove these propositions
3. the generalized `e`, which refers to these fvars

The `generalizations` array in the `MGen` is completely managed by this function.
The `propToProof` map is updated with the new proposition fvars.
-/
def withGeneralizedProofs {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToProof := (← get).propToProof
  modify fun s => { s with generalizations := #[] }
  trace[Tactic.generalize_proofs] "pre-abstracted{indentD e}\npropToProof: {propToProof.toArray}"
  let e ← abstractProofs e ty? |>.run
  trace[Tactic.generalize_proofs] "post-abstracted{indentD e}"
  let generalizations := (← get).generalizations
  trace[Tactic.generalize_proofs] "new generalizations: {generalizations}"
  let decls := generalizations.map fun (name, ty, _) => (name, fun _ => pure ty)
  withLocalDeclsD decls fun fvars => do
    let mut propToProof := propToProof
    let mut map : ExprMap Expr := {}
    for (_, _, pf) in generalizations, x in fvars do
      map := map.insert pf x
      propToProof := propToProof.insert (← instantiateMVars (← inferType x)).cleanupAnnotations x
    modify fun s => { s with propToProof }
    trace[Tactic.generalize_proofs] "replacing. map: {map.toArray}\nbefore: e = {e}"
    let e' := e.replace map.find?
    trace[Tactic.generalize_proofs] "after: e = {e}"
    k fvars (generalizations.map fun (_, _, pf) => pf) e'

/--
Main loop for `Lean.MVarId.generalizeProofs`.
The `fvars` array is the array of fvars to generalize proofs for,
and `rfvars` is the array of fvars that have been reverted.
The `g` metavariable has all of these fvars reverted.
-/
partial def generalizeProofsCore
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array FVarId × MVarId) :=
  go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array FVarId) : MGen (Array FVarId × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      trace[Tactic.generalize_proofs] "generalizeProofsCore {i}{g}\n{(← get).propToProof.toArray}"
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := tgt.bindingDomain!.cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          -- Clear the proof value (using proof irrelevance) and `go` again
          let tgt' := Expr.forallE tgt.bindingName! ty tgt.bindingBody! tgt.bindingInfo!
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToProof.find? ty then
          -- Eliminate this local hypothesis using the pre-existing proof, using proof irrelevance
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        -- Now the main case, handling forall or let
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              -- Make this prop available as a proof
              modify fun s => { s with propToProof := s.propToProof.insert t' (.fvar fvar') }
            go g' (i + 1) (hs ++ hs'.map Expr.fvarId!)
        | .letE n t v b _ =>
          withGeneralizedProofs t none fun hs' pfs' t' => do
            withGeneralizedProofs v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g') (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs'.map Expr.fvarId! ++ hs''.map Expr.fvarId!)
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      trace[Tactic.generalize_proofs] "generalizeProofsCore target{g}\n{(← get).propToProof.toArray}"
      withGeneralizedProofs (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
        return (hs ++ hs'.map Expr.fvarId!, g'.mvarId!)
    else
      return (hs, g)


end GeneralizeProofs

/--
Generalize proofs in the hypotheses `fvars` and, if `target` is true, the target.
Uses `names` for the names of the proofs that are generalized.

If a hypothesis is a proposition and a `let` binding, this will clear the value of the let binding.

If a hypothesis is a proposition that already appears in the local context, it will be eliminated.
-/
partial def _root_.Lean.MVarId.generalizeProofs
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (names : List (Option Name)) :
    MetaM (Array FVarId × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { nextNames := names, propToProof := ← GeneralizeProofs.initialPropToProof }
    GeneralizeProofs.generalizeProofsCore g fvars rfvars target |>.run' s

/--
Generalizes proofs in the current goal.
- `generalize_proofs` generalizes proofs in the target.
- `generalize_proofs at h₁ h₂ ⊢` generalized proofs in hypotheses `h₁` and `h₂` as well as the goal.
- `generalize_proofs pf₁ pf₂ pf₃` uses names `pf₁`, `pf₂`, and `pf₃` for the generalized proofs.
  These can be `_` to not name proofs.

If a proof is already present in the local context, it will use that rather than generating a new
local hypothesis.

When doing `generalize_proofs at h`, if `h` is a let binding, its value is cleared,
and furthermore if `h` is a duplicate of a preceding local hypothesis, it is eliminated.

For example:
```lean
example : List.nthLe [1, 2] 1 (by simp) = 2 := by
  -- ⊢ [1, 2].nthLe 1 ⋯ = 2
  generalize_proofs h
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```
-/
elab (name := generalizeProofsElab) "generalize_proofs"
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let names := hs |>.map (fun | `(binderIdent| $s:ident) => some s.getId | _ => none) |>.toList
  let loc := expandOptLocation (Lean.mkOptionalNode loc?)
  let (fvars, target) ←
    match loc with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← g.generalizeProofs fvars target names
    for h in hs, fvar in pfs do
      g.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
    return g
