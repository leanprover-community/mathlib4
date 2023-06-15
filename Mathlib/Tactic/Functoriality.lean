import Mathlib.Tactic.Functoriality.Attr
import Mathlib.Tactic.SolveByElim
import Mathlib.GroupTheory.Submonoid.Operations

attribute [functor] Submonoid.map Submonoid.comap

open Lean Meta Elab Tactic
open Mathlib Tactic LabelAttr

def solveUsingFunctors (g : MVarId) : MetaM Unit := do
  let cfg : SolveByElim.Config :=
    { maxDepth := 30, symm := true, allowSynthFailures := true }
  let cfg := cfg.synthInstance
  let [] ← SolveByElim.solveByElim.processSyntax cfg false false [] [] #[mkIdent `functor] [g]
    | throwError "solve_by_elim returned subgoals: this should be impossible!"

elab "functoriality" : tactic => do
  liftMetaFinishingTactic solveUsingFunctors

set_option trace.Meta.Tactic.solveByElim true

example [Monoid M] [Monoid N] (f : M →* N) : Submonoid M → Submonoid N := by
  functoriality
