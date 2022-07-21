/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Derives `Inhabited α` from `Nonempty α` with `Classical.choice`-/
noncomputable def nonempty_to_inhabited (α : Type _) (_ : Nonempty α) : Inhabited α :=
  Inhabited.mk (Classical.ofNonempty)

/-- Derives `Inhabited α` from `Nonempty α` without `Classical.choice` assuming `α` is of type `Prop`-/
def nonempty_prop_to_inhabited (α : Prop) (α_nonempty : Nonempty α) : Inhabited α :=
  Inhabited.mk <| Nonempty.elim α_nonempty id

/-- `inhabit α` tries to derive a `Nonempty α` instance and then uses it to make an `Inhabited α` instance.
     If the target is a `Prop`, this is done constructively. Otherwise, it uses `Classical.choice`.
-/
syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic

/-- inhabitCore takes in the mVarId of the main goal, runs the core portion of the inhabit tactic,
    and returns the resulting mVarId -/
def inhabitCore (mVarId : MVarId) (h_name : Option Ident) (term : Syntax) : TacticM MVarId := do
  withMVarContext mVarId do
    let e ← Tactic.elabTerm term none
    let e_lvl ← Meta.getLevel e
    let inhabited_e := mkApp (mkConst ``Inhabited [e_lvl]) e
    let nonempty_e := mkApp (mkConst ``Nonempty [e_lvl]) e
    let nonempty_e_pf ← synthInstance nonempty_e
    let h_name : Name :=
      match h_name with
      | some h_name => h_name.getId
      | none => `inhabited_h
    let pf ←
      if ← isProp e then Meta.mkAppM ``nonempty_prop_to_inhabited #[e, nonempty_e_pf]
      else Meta.mkAppM ``nonempty_to_inhabited #[e, nonempty_e_pf]
    let (_, mVarId2) ← intro1P (← assert mVarId h_name inhabited_e pf)
    return mVarId2

elab_rules : tactic
  | `(tactic| inhabit $[$h_name:ident :]? $term) => do
    let mVarId ← inhabitCore (← getMainGoal) h_name term
    replaceMainGoal [mVarId]
