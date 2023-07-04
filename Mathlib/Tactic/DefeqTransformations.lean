/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Tactic.Basic

/-! # Tactics that do definitional transformations

This module defines a standard wrapper that can be used to create tactics that
change hypotheses and the goal definitionally.

It then provides a number of tactics that transform local hypotheses and/or the target.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Elab.Tactic

/-- For the main goal, use `m` to transform the types of locations specified by `loc?`.
If `loc?` is none, then transforms the type of target. `m` is provided with an expression
with instantiated metavariables.

`m` *must* transform expressions to defeq expressions. `runDefeqTactic` will throw
an error if the result is not defeq. -/
def runDefeqTactic (m : Expr → MetaM Expr)
    (loc? : Option (TSyntax ``Parser.Tactic.location))
    (tacticName : String) :
    TacticM Unit := withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc?))
    (atLocal := fun h => liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← h.getType)
      mvarId.changeLocalDecl' h (← m ty))
    (atTarget := liftMetaTactic1 fun mvarId => do
      let ty ← instantiateMVars (← mvarId.getType)
      mvarId.change (← m ty))
    (failed := fun _ => throwError "{tacticName} failed")


/-! ### `whnf` -/

/--
`whnf at loc` puts the given location into weak-head normal form.

This is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.
-/
elab "whnf" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefeqTactic Meta.whnf loc? "whnf"


/-! ### `beta_reduce` -/

/--
`beta_reduce at loc` completely beta reduces the given location.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.
-/
elab "beta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefeqTactic (Core.betaReduce ·) loc? "beta_reduce"


/-! ### `reduce` -/

/--
`reduce at loc` completely reduces the given location.

This does the same transformation at the `#reduce` command.
-/
elab "reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefeqTactic (Meta.reduce · (skipTypes := false) (skipProofs := false)) loc? "reduce"


/-! ### `unfold_let` -/

/-- Unfold all the fvars from `fvars` in `e` that have local definitions (are "let-bound"). -/
def unfoldFVars (fvars : Array FVarId) (e : Expr) : MetaM Expr := do
  transform (usedLetOnly := true) e fun node =>
    match node with
    | .fvar fvarId =>
      if fvars.contains fvarId then
        (TransformStep.continue ·) <$> (fvarId.getValue? >>= Option.mapM instantiateMVars)
      else
        pure TransformStep.continue
    | _ => pure TransformStep.continue

/--
`unfold_let x y z at loc` unfolds the local definitions `x`, `y`, and `z` at the given
location. This is known as "zeta reduction."

If no local definitions are given, then all local definitions are unfolded.

The `unfold` tactic instead is for unfolding global definitions.
-/
syntax "unfold_let" (ppSpace colGt term:max)* (ppSpace Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| unfold_let $[$loc?]?) =>
    runDefeqTactic Meta.zetaReduce loc? "unfold_let"
  | `(tactic| unfold_let $hs:term* $[$loc?]?) => do
    runDefeqTactic (unfoldFVars (← getFVarIds hs)) loc? "unfold_let"


/-! ### `unfold_projs` -/

/-- Recursively unfold all the projection applications for class instances. -/
def unfoldProjs (e : Expr) : MetaM Expr := do
  transform e fun node => do
    (TransformStep.continue ·) <$> (Meta.unfoldProjInst? node >>= Option.mapM instantiateMVars)

/--
`unfold_projs at loc` unfolds projections of class instances at the given location.
-/
elab "unfold_projs" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefeqTactic unfoldProjs loc? "unfold_projs"


/-! ### `eta_reduce` -/

/-- Eta reduce everything -/
def etaReduceAll (e : Expr) : MetaM Expr := do
  transform e fun node => pure <| TransformStep.continue node.etaExpanded?

/--
`eta_reduce at loc` eta reduces all sub-expressions at the given location.

For example, `fun x y => f x y` becomes `f` after eta reduction.
-/
elab "eta_reduce" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefeqTactic etaReduceAll loc? "eta_reduce"


-- /-! ### `eta_expand` -/

-- def etaExpandAll (e : Expr) : MetaM Expr := do
--   transform e fun node =>
--     TransformStep.done <$> Meta.etaExpand node

end Mathlib.Tactic
