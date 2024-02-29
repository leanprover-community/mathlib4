/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity.Core

/-!
# Positivity extensions for finsets

This file provides a few `positivity` extensions that cannot be in either the finset files (because
they don't know about ordered fields) or in `Tactic.Positivity.Basic` (because it doesn't want to
know about finiteness).
-/

namespace Mathlib.Meta.Positivity

open Qq Lean Meta Finset

/-- Extension for `Finset.card`. `s.card` is positive if `s` is nonempty.

It calls `Mathlib.Meta.proveFinsetNonempty` to attempt proving that the finset is nonempty. -/
@[positivity Finset.card _]
def evalFinsetCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Finset.card $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assertInstancesCommute
    return .positive q(Finset.Nonempty.card_pos $ps)
  | _ => throwError "not Finset.card"

/-- Extension for `Fintype.card`. `Fintype.card α` is positive if `α` is nonempty. -/
@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Fintype.card $β $instβ) =>
    let instβno ← synthInstanceQ q(Nonempty $β)
    assumeInstancesCommute
    return .positive q(@Fintype.card_pos $β $instβ $instβno)
  | _ => throwError "not Fintype.card"

example {α : Type*} {s : Finset α} (hs : s.Nonempty) : 0 < s.card := by positivity
example {α : Type*} {s : Finset α} : 0 ≤ s.card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < (univ : Finset α).card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity
example {α : Type*} [Fintype α] : 0 ≤ Fintype.card α := by positivity

example {G : Type*} {A : Finset G} :
  let f := fun _ : G ↦ 1; (∀ s, f s ^ 2 = 1) → 0 ≤ A.card := by
  intros
  positivity -- Should succeed despite failing to prove `A` is nonempty.

end Mathlib.Meta.Positivity
