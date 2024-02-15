import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity.Core

open Finset
namespace Mathlib.Meta.Positivity
open Qq Lean Meta

@[positivity Finset.card _]
def evalFinsetCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Finset.card $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assertInstancesCommute
    return .positive q(Finset.Nonempty.card_pos $ps)
  | _ => throwError "not Finset.card"

@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Fintype.card $β $instβ) =>
    let instβno ← synthInstanceQ q(Nonempty $β)
    assumeInstancesCommute
    return .positive q(@Fintype.card_pos $β $instβ $instβno)
  | _ => throwError "not Fintype.card"

example {α : Type*} {s : Finset α} (hs : s.Nonempty) : 0 < s.card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < (univ : Finset α).card := by positivity
example {α : Type*} [Fintype α] [Nonempty α] : 0 < Fintype.card α := by positivity

end Mathlib.Meta.Positivity
