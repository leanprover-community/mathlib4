import Mathlib.Tactic
import Lean

open Lean Meta Elab Tactic Term

/--
This function is similar to `forallMetaTelescopeReducingUntilDefEq` except that
it will construct mvars until it reaches one whose type is defeq to the given
type `t`. It uses `forallMetaTelescopeReducing`.
-/
def Lean.Meta.forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let mut mvs : Array Expr := #[]
  let mut bis : Array BinderInfo := #[]
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do throwError "Error"
  mvs := ms
  bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do throwError "Error"
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

namespace Mathlib.Tactic

elab "apply" t:term "at" i:ident : tactic => withMainContext do
  let f ← Term.elabTerm t none
  let ldecl ← (← getLCtx).findFromUserName? i.getId
  let (mvs, _, tp) ← forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
  let mainGoal ← getMainGoal
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  let mainGoal ← mainGoal.assert ldecl.userName tp (mkAppN f (mvs.pop.push ldecl.toExpr))
  let (_, mainGoal) ← mainGoal.intro1P
  replaceMainGoal <| [mainGoal] ++ mvs.pop.toList.map fun e => e.mvarId!

variable (α β γ δ : Type*) (f : α → β → γ → δ)

example (g : γ) (a : α) (b : β) : δ := by
  apply f at g
  exact g
  exact a
  exact b

open Nat

theorem succ_inj2 (a b : Nat) : succ a = succ b → a = b := by simp

example (a b : Nat) (h : succ a = succ b) : a = b := by
  apply succ_inj2 at h
  exact h

example (A B C : Prop) (ha : A) (f : A → B) (g : B → C) : C := by
  apply f at ha
  apply g at ha
  exact ha
