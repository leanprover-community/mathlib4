/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import Mathlib.Tactic.CategoryTheory.Monoidal.Normalize
import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize

/-!
# A `coherence` tactic for monoidal categories

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

-/

namespace Mathlib.Tactic.BicategoryLike

open Lean Meta Elab Tactic
open Mathlib.Tactic.Monoidal
open Mathlib.Tactic.Bicategory


inductive Kind where
  | monoidal : Kind
  | bicategory : Kind

def Kind.name : Kind → Name
  | Kind.monoidal => `monoidal
  | Kind.bicategory => `bicategory

def mkKind (e : Expr) : MetaM Kind := do
  let e ← instantiateMVars e
  let e ← (match (← whnfR e).eq? with
    | some (_, lhs, _) => return lhs
    | none => return e)
  let ctx? ← mkContext? (ρ := Bicategory.Context) e
  match ctx? with
  | .some _ => return .bicategory
  | .none =>
    let ctx? ← mkContext? (ρ := Monoidal.Context) e
    match ctx? with
    | .some _ => return .monoidal
    | .none => throwError "failed to construct a monoidal category or bicategory context from {e}"

def pureCoherenceMain (mvarId : MVarId) : MetaM (List MVarId) := do
  let k ← mkKind (← mvarId.getType)
  withTraceNode k.name (fun _ => return m!"{checkEmoji} {k.name}") do
    match k with
    | .monoidal => Monoidal.pureCoherence mvarId
    | .bicategory => Bicategory.pureCoherence mvarId

elab "pure_coherence" : tactic => withMainContext do
  replaceMainGoal <| ← pureCoherenceMain <| ← getMainGoal

def coherence (mvarId : MVarId) : MetaM (List MVarId) := do
  let k ← mkKind (← mvarId.getType)
  withTraceNode k.name (fun _ => return m!"{checkEmoji} {k.name}") do
    match k with
    | .monoidal => Monoidal.monoidal mvarId
    | .bicategory => Bicategory.bicategory mvarId

elab "coherence" : tactic => withMainContext do
  replaceMainGoal <| ← coherence <| ← getMainGoal

end Mathlib.Tactic.BicategoryLike
