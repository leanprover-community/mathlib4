module

public import Mathlib.Tactic.ClickSuggestions.Util

/-!
This file tests `isExplicitEq`, the function used to decide when two expressions are the same
and should be deduplicated.
-/

open Lean Meta Elab

elab "check_same" e₁:term ", " e₂:term : command => Command.runTermElabM fun _ ↦ do
  let e₁ ← Term.elabTerm e₁ none; let e₂ ← Term.elabTerm e₂ none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e₁ ← instantiateMVars e₁; let e₂ ← instantiateMVars e₂
  guard <| ← Mathlib.Tactic.ClickSuggestions.isExplicitEq e₁ e₂

elab "check_not_same" e₁:term ", " e₂:term : command => Command.runTermElabM fun _ ↦ do
  let e₁ ← Term.elabTerm e₁ none; let e₂ ← Term.elabTerm e₂ none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e₁ ← instantiateMVars e₁; let e₂ ← instantiateMVars e₂
  guard !(← Mathlib.Tactic.ClickSuggestions.isExplicitEq e₁ e₂)

variable (a b : Nat)

check_not_same PUnit.{0}, PUnit.{1}
check_not_same a ≤ b, b ≥ a
check_not_same 1 + 1, 2
check_not_same (1 : Nat), (1 : Int)
check_not_same ((1 : Nat) : Int), (1 : Int)
check_not_same ((1 : Nat) : Rat), ((1 : Int) : Rat)
check_not_same
  1,
  have : One Nat := ⟨0 + 1 + 0⟩; 1


check_same
  1,
  haveI : One Nat := ⟨0 + 1 + 0⟩; 1
check_same
  fun _x : Int ↦ 1,
  fun _y : Int ↦ haveI : One Nat := ⟨0 + 1 + 0⟩; 1
check_same
  ∀ x : Nat, x = 1,
  ∀ x : Nat, x = haveI : One Nat := ⟨0 + 1 + 0⟩; 1
