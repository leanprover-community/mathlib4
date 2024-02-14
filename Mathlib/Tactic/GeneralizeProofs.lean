/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean.Meta.AbstractNestedProofs
import Mathlib.Lean.Expr.Basic

/-!
# The `generalize_proofs` tactic

Generalize any proofs occurring in the goal or in chosen hypotheses, replacing them by
named hypotheses so that they can be referred to later in the proof easily.
Commonly useful when dealing with functions like `Classical.choose` that produce data from proofs.

For example:
```lean
example : List.nthLe [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nthLe 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```
-/

namespace Mathlib.Tactic.GeneralizeProofs
open Lean Meta Elab Parser.Tactic Elab.Tactic

/- The following set up are the visit function are based on the file
Lean.Meta.AbstractNestedProofs in core -/

/-- State for the generalize proofs tactic, contains the remaining names to be used and the
list of generalizations so far -/
structure State where
  /-- The user provided names, may be anonymous -/
  nextIdx : List (TSyntax ``binderIdent)
  /-- The generalizations made so far -/
  curIdx : Array GeneralizeArg := #[]

/-- Monad used by the `generalizeProofs` tactic, carries an expr cache and state with
names to use and previous generalizations -/
abbrev M := MonadCacheT ExprStructEq Expr <| StateRefT State MetaM

/-- generalize the given e -/
private def mkGen (e : Expr) : M Unit := do
  let s ← get
  let t ← match s.nextIdx with
  | [] => mkFreshUserName `h
  | n :: rest =>
    modify fun s ↦ { s with nextIdx := rest }
    match n with
    | `(binderIdent| $s:ident) => pure s.getId
    | _ => mkFreshUserName `h
  modify fun s ↦ { s with curIdx := s.curIdx.push ⟨e, t, none⟩ }

/-- Recursively generalize proofs occurring in e -/
partial def visit (e : Expr) : M Expr := do
  if e.isAtomic then
    pure e
  else
    let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do
      let localInstances ← getLocalInstances
      let mut lctx ← getLCtx
      for x in xs do
        let xFVarId := x.fvarId!
        let localDecl ← xFVarId.getDecl
        let type      ← visit localDecl.type
        let localDecl := localDecl.setType type
        let localDecl ← match localDecl.value? with
           | some value => let value ← visit value; pure <| localDecl.setValue value
           | none       => pure localDecl
        lctx := lctx.modifyLocalDecl xFVarId fun _ ↦ localDecl
      withLCtx lctx localInstances k
    checkCache (e : ExprStructEq) fun _ ↦ do
      if (← AbstractNestedProofs.isNonTrivialProof e) then
        mkGen e
        return e
      else match e with
        | .lam ..      => lambdaLetTelescope e fun xs b ↦ visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .letE ..     => lambdaLetTelescope e fun xs b ↦ visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .forallE ..  => forallTelescope e fun xs b ↦ visitBinders xs do
          mkForallFVars xs (← visit b)
        | .mdata _ b   => return e.updateMData! (← visit b)
        | .proj _ _ b  => return e.updateProj! (← visit b)
        | .app ..      => e.withApp fun f args ↦ return mkAppN f (← args.mapM visit)
        | _            => pure e

/--
Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : List.nthLe [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nthLe 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```
-/
elab (name := generalizeProofs) "generalize_proofs"
    hs:(ppSpace colGt binderIdent)* loc:(location)? : tactic => do
  let ou := if loc.isSome then
    match expandLocation loc.get! with
    | .wildcard => #[]
    | .targets t _ => t
  else #[]
  let fvs ← getFVarIds ou
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let (_, ⟨_, out⟩) ← GeneralizeProofs.visit ty |>.run.run { nextIdx := hs.toList }
  let (_, fvarIds, goal) ← goal.generalizeHyp out fvs
  for h in hs, fvar in fvarIds do
    goal.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
  replaceMainGoal [goal]
