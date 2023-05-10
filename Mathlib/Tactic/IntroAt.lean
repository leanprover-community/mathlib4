/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.Basic

/-!
# The `intro at` tactic

This module defines a tactic `intro ... at h` that can be used to (in essence) do `cases`
on a `let` expression.
-/


open Lean Elab Parser Meta Tactic

/-- Given a local hypothesis that can in some sense be introed (like one with a type that is
a `let`), then create a new local hypothesis with that introduced variable.

So far `let` is all `introAt` can handle, but it could be extended to handle constructs such as
`Exists` and `Sigma`, which are one-constructor inductive types whose constructor has
two arguments. -/
def Lean.MVarId.introAt (mvarId : MVarId) (fvarId : FVarId) (name : Name) :
    MetaM (FVarId × MVarId) := do
  mvarId.checkNotAssigned `introAt
  mvarId.withReverted #[fvarId] fun mvarId fvarids => mvarId.withContext do
    let ty ← Lean.instantiateMVars (← mvarId.getType)
    let mvarId ← match ty with
      | .letE n (.letE n' t' v' b' _) v b ndep =>
        -- Lift the let over the let
        withLetDecl n' t' v' fun fvar => do
          let b' := b'.instantiate1 fvar
          let ty' ← mkLetFVars #[fvar] <| .letE n b' v b ndep
          mvarId.change ty'
      | .letE .. => throwTacticEx `introAt mvarId "local let binding must be a `let`"
      | .forallE n (.letE n' t' v' b' _) v b =>
        -- Lift the let over the forall
        withLetDecl n' t' v' fun fvar => do
          let b' := b'.instantiate1 fvar
          let ty' ← mkLetFVars #[fvar] <| .forallE n b' v b
          mvarId.change ty'
      | .forallE .. => throwTacticEx `introAt mvarId "local variable must be a `let`"
      | _ => throwTacticEx `introAt mvarId "unexpected auxiliary target"
    let (fvarId, mvarId) ← mvarId.intro name
    return (fvarId, fvarids.map .some, mvarId)

namespace Mathlib

/-- The `intro ... at ...` tactic is for introducing additional local hypotheses associated
to a given local hypothesis. The primary use is to lift `let`s into the local context, and
it can be thought of as being a `cases` tactic for `let`s.

For example, if `h : let x := 1; x = x`, then `intro x at h` introduces `x : Nat := 1` and changes
`h` to `h : x = x`.

The tactic `intro at ⊢` raises an error; one should instead use the `intro`. -/
syntax (name := introAt) "intro " notFollowedBy("|") (colGt term:max)* (ppSpace location) : tactic

@[tactic Mathlib.introAt] def evalIntroAt : Tactic := fun stx => do
  match stx with
  | `(tactic| intro $loc:location)                   => introStep none `_ loc
  | `(tactic| intro $h:ident $loc:location)          => introStep h h.getId loc
  | `(tactic| intro _%$tk $loc:location)             => introStep tk `_ loc
  | `(tactic| intro $h:term $hs:term* $loc:location) =>
    evalTactic (← `(tactic| intro $h:term $loc:location; intro $hs:term* $loc:location))
  | _ => throwUnsupportedSyntax
where
  introStep (ref : Option Syntax) (n : Name) (loc : TSyntax `Lean.Parser.Tactic.location) :
      TacticM Unit := do
    withLocation (expandOptLocation (mkOptionalNode loc))
      (atLocal := fun h ↦ do
        let fvarId ← liftMetaTacticAux fun mvarId => do
          let (fvarId, mvarId) ← mvarId.introAt h n
          return (fvarId, [mvarId])
        if let some stx := ref then Term.addLocalVarInfo stx (.fvar fvarId))
      (atTarget := throwError "use the `intro` tactic rather than `intro at ⊢`")
      (failed := fun _ ↦ throwError "intro at tactic failed")

end Mathlib
