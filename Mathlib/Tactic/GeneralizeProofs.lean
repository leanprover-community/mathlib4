/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean
import Mathlib.Tactic.LibrarySearch


/-!
# The `generalize_proofs` tactic

Generalize any proofs occuring in the goal or in chosen hypotheses, replacing them by
named hypotheses so that they can be referred to later in the proof easily.
Commonly useful when dealing with functions like `Classical.choose` that produce data from proofs.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
```
-/

open Lean.Meta

namespace Lean.Elab.Tactic

-- unrelated to this file but nice for debugging
deriving instance Repr for GeneralizeArg

namespace GeneralizeProofs

/- The following set up are the visit function are based on the file
Lean.Meta.AbstractNestedProofs in core -/

/--
Matching function for proofs to be generalized,
duplicate of `Lean.Meta.AbstractNestedProofs.isNonTrivialProof` -/
def isNonTrivialProof (e : Expr) : MetaM Bool := do
  if !(← isProof e) then
    pure false
  else
    e.withApp fun f args =>
      pure $ !f.isAtomic || args.any fun arg => !arg.isAtomic

/-- State for the generalize proofs tactic, contains the remaining names to be used and the
list of generalizations so far -/
structure State where
  /-- The user provided names, may be anonymous -/
  nextIdx : Array Name
  /-- The generalizations made so far -/
  curIdx : Array GeneralizeArg := #[]

/-- Monad used by the `generalizeProofs` tactic, carries an expr cache and state with
names to use and previous generalizations -/
abbrev M := MonadCacheT ExprStructEq Expr $ StateRefT State MetaM

/-- generalize the given e -/
private def mkGen (e : Expr) : M Unit := do
  let s ← get
  let mut t := Name.anonymous
  if s.nextIdx = #[] then
    t ← mkFreshUserName `h
  modify fun s =>
    { s with
      nextIdx := s.nextIdx.pop,
      curIdx := s.curIdx.push ⟨e, s.nextIdx.back?.getD t, none⟩ }

/-- Recursively generalize proofs occuring in e -/
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
        lctx := lctx.modifyLocalDecl xFVarId fun _ => localDecl
      withLCtx lctx localInstances k
    checkCache { val := e : ExprStructEq } fun _ => do
      if (← isNonTrivialProof e) then
        mkGen e
        return e
      else match e with
        | .lam ..      => lambdaLetTelescope e fun xs b => visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .letE ..     => lambdaLetTelescope e fun xs b => visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .forallE ..  => forallTelescope e fun xs b => visitBinders xs do
          mkForallFVars xs (← visit b)
        | .mdata _ b   => return e.updateMData! (← visit b)
        | .proj _ _ b  => return e.updateProj! (← visit b)
        | .app ..      => e.withApp fun f args => return mkAppN f (← args.mapM visit)
        | _            => pure e

end GeneralizeProofs

open Lean.Parser.Tactic

/--
Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
```
-/
elab (name := generalizeProofs) "generalize_proofs"
  hs:(ppSpace (colGt binderIdent))* loc:(ppSpace location)? : tactic => do
    let ou := if loc.isSome then
        match expandLocation loc.get! with
          | .wildcard => #[]
          | .targets t _ => t
      else #[]
    let fvs ← getFVarIds ou
    liftMetaTactic1 fun goal => do -- TODO decide if working on all or not
      let hsa : Array Name ← (hs.reverse.mapM fun sy => do
        if let `(binderIdent| $s:ident) := sy then
          return s.getId
        else
          mkFreshUserName `h)
      let (_, ⟨_, out⟩) ← GeneralizeProofs.visit (← instantiateMVars (← goal.getType)) |>.run |>.run
        { nextIdx := hsa }
      let (_, _, mvarId) ← goal.generalizeHyp out fvs
      return mvarId
