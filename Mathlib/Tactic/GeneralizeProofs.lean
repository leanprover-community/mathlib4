/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean
import Mathlib.Tactic.LibrarySearch

open Lean.Meta

namespace Lean.Elab.Tactic

deriving instance Repr for GeneralizeArg
namespace GeneralizeProofs

def isNonTrivialProof (e : Expr) : MetaM Bool := do
  if !(← isProof e) then
    pure false
  else
    e.withApp fun f args =>
      pure $ !f.isAtomic || args.any fun arg => !arg.isAtomic

structure Context where
  baseName : Name

structure State where
  nextIdx : Array Name
  curIdx : Array GeneralizeArg := #[]

abbrev M := ReaderT Context $ MonadCacheT ExprStructEq Expr $ StateRefT State MetaM

private def mkGen (e : Expr) : M Unit := do
  -- let ctx ← read
  let s ← get
  -- let lemmaName ← mkAuxName (ctx.baseName ++ `proof) s.nextIdx
  logInfo e
  logInfo (toMessageData s.nextIdx)
  let mut t := Name.anonymous
  if s.nextIdx = #[] then
    t ← mkFreshUserName `h
  modify fun s =>
    { s with nextIdx := s.nextIdx.pop, curIdx := s.curIdx.push ⟨e, s.nextIdx.back?.getD t, none⟩ }
  /- We turn on zeta-expansion to make sure we don't need to perform an expensive `check` step to
     identify which let-decls can be abstracted. If we design a more efficient test, we can avoid
     the eager zeta expasion step.
     It a benchmark created by @selsam, The extra `check` step was a bottleneck. -/
  -- mkAuxDefinitionFor lemmaName e (zeta := true)

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
    logInfo (toMessageData ou)
    liftMetaTactic1 fun goal => do -- TODO decide if working on all or not
      let hsa : Array Name ← (hs.reverse.mapM fun sy => do
        if let `(binderIdent| $s:ident) := sy then
          return s.getId
        else
          mkFreshUserName `h)
      logInfo (toMessageData hsa)
      logInfo (← goal.getType)
      logInfo (← (do let t ← goal.getType; instantiateMVars t))
      let (_, ⟨_, out⟩) ← GeneralizeProofs.visit (← instantiateMVars (← goal.getType)) |>.run
        { baseName := `a } |>.run |>.run { nextIdx := hsa }
      let (_, _, mvarId) ← goal.generalizeHyp out fvs --fvarIds
      logInfo (toMessageData hs)
      return mvarId
