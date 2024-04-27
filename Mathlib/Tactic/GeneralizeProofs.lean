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
  These should all be valid with respect to the local context outside `abstractProofs`. -/
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
For example, `(by simp : 1 < [1, 2].length)` has `1 < Nat.succ 1` as the inferred type,
but from knowing it's an argument to `List.nthLe` we can deduce `1 < [1, 2].length`.
-/
partial def abstractProofs (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  visit (← instantiateMVars e) ty? #[]
where
  /--
  Core implementation of `abstractProofs`.
  - `fvars` is the current list of bound variables.
  -/
  visit (e : Expr) (ty? : Option Expr) (fvars : Array Expr) : MAbs Expr := do
    if e.isAtomic then
      return e
    else
      checkCache e fun _ ↦ do
        let ty ← ty?.getDM (inferType e)
        if ← isProof e then
          visitProof e ty fvars
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none fvars) fun x ↦ do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none (fvars.push x))
          | .lam n t b i => do
            withLocalDecl n i (← visit t none fvars) fun x ↦ do
              let ty ← whnfD ty
              if !ty.isForall then panic! "Expecting forall in abstractProofs .lam"
              let ty' := ty.instantiate1 x
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty' (fvars.push x))
          | .letE n t v b _ =>
            let t' ← visit t none fvars
            withLetDecl n t' (← visit v t' fvars) fun x ↦ do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty (fvars.push x))
          | .app .. =>
            e.withApp fun f args ↦ do
              -- For simplicity, don't try to propagate the type into the function.
              let f' ← visit f none fvars
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
                  unifiedTy := (← liftMetaM <| observing? <| isDefEq fty ty).getD false
                let argTy := (← instantiateMVars <| ← inferType args'[i]!).cleanupAnnotations
                let arg' ← visit args[i]! argTy fvars
                unless ← isDefEq argTy (← inferType arg') do
                  panic! s!"failed isDefEq for .app {i}, {← ppExpr args'[i]!}, {← ppExpr args[i]!}"
                args'[i]!.mvarId!.assign arg'
              instantiateMVars <| mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty fvars)
          -- Giving up propagating expected types for `.proj`, which we shouldn't see anyway
          | .proj _ _ b => return e.updateProj! (← visit b none fvars)
          | _           => unreachable!
  /-- Removes any mdata that appears in an application. -/
  stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | .app f x => .app (stripMData f).headBeta x
  | e => e
  /-- If `e` is the result of `mkLambdaFVars args ...`,
  returns `e'` and `args'` where variables from `e` have been eliminated and `args'`
  is a sublist of `args`, such that `mkAppN e' args'` is well-typed. -/
  elimUnusedArgs (e : Expr) (args : List Expr) : MetaM (Expr × List Expr) := do
    match args with
    | [] => return (e, [])
    | arg :: args =>
      match e with
      | .letE _ _ v b _ => elimUnusedArgs (b.instantiate1 v) args
      | .lam n t b i =>
        if b.hasLooseBVars then
          withLocalDecl n i t fun x => do
            let (b', args') ← elimUnusedArgs (b.instantiate1 x) args
            return (← mkLambdaFVars #[x] b', arg :: args')
        else
          elimUnusedArgs b args
      | _ => unreachable!
  /--
  Core implementation of abstracting a proof.
  -/
  visitProof (e ty : Expr) (fvars : Array Expr) : MAbs Expr := do
    -- -- 1. zeta reduce to ensure that there are no dependencies on lets from `fvars`.
    -- let e ←
    --     Meta.transform (usedLetOnly := true) e fun node => do
    --       match node with
    --       | .fvar fvarId =>
    --         if fvars.contains node then
    --           if let some val ← fvarId.getValue? then
    --             return .visit val
    --         return .done node
    --       | _ => return .continue
    -- 2. do some simplifications of e
    let e := e.withApp' fun f args => f.beta args
    -- 3. if head is atomic and arguments are bound variables, then no use in abstracting
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then
      return e
    -- 4. abstract `fvars` out of `e` to make the abstracted proof `pf`
    let e ← mkExpectedTypeHint e ty
    --let usedFVars := (collectFVars {} e).fvarSet -- this might not be right
    --let fvars' := fvars.filter (fun fvar => usedFVars.contains fvar.fvarId!)
--    let fvars' ← fvars.filterM fun fvar => return !(← fvar.fvarId!.getDecl).isLet
    let (pf, fvars') ← elimUnusedArgs (← mkLambdaFVars fvars e) fvars.toList
    let pfTy ← instantiateMVars (← inferType pf)
    -- 5. check if there is already a recorded proof for this proposition.
    trace[Tactic.generalize_proofs] "finding {pfTy}"
    if let some pf' := (← get).propToProof.find? pfTy then
      trace[Tactic.generalize_proofs] "5 found proof"
      return mkAppN pf' fvars'.toArray
    -- 6. record the proof in the state and return the proof.
    let name ← (← nextName?).getDM (mkFreshUserName `h)
    modify fun s =>
      { s with
        propToProof := s.propToProof.insert pfTy pf
        generalizations := s.generalizations.push (name, pfTy, pf) }
    trace[Tactic.generalize_proofs] "6 added"
    return mkAppN pf fvars'.toArray

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
partial def withGeneralizedProofs {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToProof := (← get).propToProof
  modify fun s => { s with generalizations := #[] }
  trace[Tactic.generalize_proofs] "pre-abstracted{indentD e}\npropToProof: {propToProof.toArray}"
  let e ← abstractProofs e ty? |>.run
  trace[Tactic.generalize_proofs] "post-abstracted{indentD e}"
  let generalizations := (← get).generalizations
  trace[Tactic.generalize_proofs] "new generalizations: {generalizations}"
  let rec
    /-- Core loop for `withGeneralizedProofs`, adds generalizations one at a time. -/
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToProof : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (name, ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.find?)).cleanupAnnotations
        withLocalDeclD name ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToProof := propToProof.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.find?
          trace[Tactic.generalize_proofs] "after: e' = {e}"
          modify fun s => { s with propToProof }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToProof := propToProof)

/--
Main loop for `Lean.MVarId.generalizeProofs`.
The `fvars` array is the array of fvars to generalize proofs for,
and `rfvars` is the array of fvars that have been reverted.
The `g` metavariable has all of these fvars reverted.
-/
partial def generalizeProofsCore
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) :=
  go g 0 #[]
where
  /-- Loop for `generalizeProofsCore`. -/
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      trace[Tactic.generalize_proofs] "generalizeProofsCore {i}{g}\n{(← get).propToProof.toArray}"
      let fvar := rfvars[i]
      if fvars.contains fvar then
        -- This is one of the hypotheses that was intentionally reverted.
        let tgt ← instantiateMVars <| ← g.getType
        let ty := tgt.bindingDomain!.cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          -- Clear the proof value (using proof irrelevance) and `go` again
          let tgt' := Expr.forallE tgt.bindingName! ty tgt.bindingBody! .default
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
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs t none fun hs' pfs' t' => do
            withGeneralizedProofs v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g') (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        -- This is one of the hypotheses that was incidentally reverted.
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      trace[Tactic.generalize_proofs] "\
        generalizeProofsCore target{g}\n{(← get).propToProof.toArray}"
      withGeneralizedProofs (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g') pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)


end GeneralizeProofs

/--
Generalize proofs in the hypotheses `fvars` and, if `target` is true, the target.
Uses `names` for the names of the proofs that are generalized.
Returns the fvars for the generalized proofs and the new goal.

If a hypothesis is a proposition and a `let` binding, this will clear the value of the let binding.

If a hypothesis is a proposition that already appears in the local context, it will be eliminated.

Only *nontrivial* proofs are generalized. These are proofs that aren't of the form `f a b ...`
where `f` is atomic and `a b ...` are bound variables.
These sorts of proofs cannot be meaningfully generalized, and also these are the sorts of proofs
that are left in a term after generalization.
-/
partial def _root_.Lean.MVarId.generalizeProofs
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (names : List (Option Name)) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { nextNames := names, propToProof := ← GeneralizeProofs.initialPropToProof }
    GeneralizeProofs.generalizeProofsCore g fvars rfvars target |>.run' s

/--
`generalize_proofs ids* [at locs]?` generalizes proofs in the current goal,
turning them into new local hypotheses.

- `generalize_proofs` generalizes proofs in the target.
- `generalize_proofs at h₁ h₂` generalized proofs in hypotheses `h₁` and `h₂`.
- `generalize_proofs at *` generalizes proofs in the entire local context.
- `generalize_proofs pf₁ pf₂ pf₃` uses names `pf₁`, `pf₂`, and `pf₃` for the generalized proofs.
  These can be `_` to not name proofs.

If a proof is already present in the local context, it will use that rather than create a new
local hypothesis.

When doing `generalize_proofs at h`, if `h` is a let binding, its value is cleared,
and furthermore if `h` duplicates a preceding local hypothesis then it is eliminated.

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
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← g.generalizeProofs fvars target names
    for h in hs, fvar in pfs do
      g.withContext <| Expr.addLocalVarInfoForBinderIdent fvar h
    return g
