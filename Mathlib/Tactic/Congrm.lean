import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic


namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

syntax (name := congrM) "congrm " term : tactic

#check forallTelescope
#check elabTermEnsuringType
#check liftMetaTactic

def congrm_core (pat : Expr) : TacticM Unit := withMainContext do
  if pat.isMVar then
  return
  else match pat with
  | .forallE name _type body _info =>
    -- `apply pi_congr; intro`
    evalTactic (← `(tactic| apply pi_congr)) -- Maybe needs better error reporting
    -- Maybe replace by `forallTelescope`
    liftMetaTactic fun mvarId => do pure [(← mvarId.intro name).2]
    congrm_core body
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
