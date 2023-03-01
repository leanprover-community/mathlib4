/-
Copyright (c) 2023 Moritz Doll, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Gabriel Ebner, Damiano Testa
-/

import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic -- only needed for tests


namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

syntax (name := congrM) "congrm " term : tactic

#check forallTelescope
#check elabTermEnsuringType
#check liftMetaTactic
#check MVarId.apply

partial def congrm_core (pat : Expr) : TacticM Unit := withMainContext do
  let binders (stx : Syntax) (xs : Array Expr) (k : Expr) : TacticM Unit := do
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      evalTactic stx
      liftMetaTactic fun mvarId => do
        pure [(← mvarId.intro localDecl.userName).2]
    congrm_core k
  if pat.isMVar then
  return
  else match pat with
  | .forallE _name _type _body _info =>
    forallTelescope pat (binders (← `(tactic| apply pi_congr)))
    -- `apply pi_congr; intro`
    --evalTactic (← `(tactic| apply pi_congr)) -- Maybe needs better error reporting
    -- Maybe replace by `forallTelescope`
    --liftMetaTactic fun mvarId => do pure [(← mvarId.intro name).2]
    --congrm_core body
  | .lam _name _type _body _info =>
    lambdaTelescope pat (binders (← `(tactic| apply funext)))
    -- `apply funext; intro`
    --evalTactic (← `(tactic| apply funext))
    --liftMetaTactic fun mvarId => do pure [(← mvarId.intro name).2]
    --congrm_core body
  | .app fn arg =>
    --evalTactic (← `(tactic| congr 1))
    --congrm_core fn
    --let fn' ← whnf fn
    --evalTactic (← `(tactic| apply congr_arg))
    -- Need to get LHS and RHS of application in the goal
    liftMetaTactic fun mvarId => do
      let list ← mvarId.apply (← mkAppOptM ``congrArg #[none, none, none, none, some fn, none])
      return list
    --congrm_core arg
    --let fn' ← elabTerm fn
    --evalTactic (← `(tactic| apply congr))
    return
  | _ =>
  return


elab_rules : tactic | `(tactic| congrm $expr:term) => withMainContext do
  evalTactic (← `(tactic| try apply Eq.to_iff))
  let e ← elabTerm expr none
  congrm_core e


example (f : α → Prop): (∀ a : α, f a) ↔ (∀ b : α, True) := by
  congrm (∀ x, _)

  --apply Eq.to_iff
  have : ∀ a, f a = True := sorry
  exact this x

example (f : α → α → Prop): (∀ a b, f a b) ↔ (∀ a b : α, True) := by
  congrm (∀ x y, _)
  have : ∀ a b, f a b = True := sorry
  exact this x y

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm (f _)
  exact h

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  --apply propext
  congr 1
  simp only [h]

example : (3 : ℤ) ≤ (3 : ℕ) := by
  simp only
