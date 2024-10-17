/-
Copyright (c) 2024 Tom Kranz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Kranz
-/
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.ULift

/-!
# FinEnum instance for Option

Provides a recursor for FinEnum types like `Fintype.truncRecEmptyOption`, but capable of producing
non-truncated data.

## TODO
* recreate rest of `Mathlib.Data.Fintype.Option`
-/

namespace FinEnum
universe u v

/-- The additional `Option.none` element doesn't negate enumerability. -/
instance instFinEnumOption (α : Type u) [FinEnum α] : FinEnum (Option α) where
  card := card α + 1
  equiv := by
    refine ⟨Option.rec 0 (Fin.succ ∘ equiv), Fin.cases none (some ∘ equiv.symm), ?_, ?_⟩
    <;> [apply Option.rec; apply Fin.cases] <;> simp[Fin.succ_ne_zero]

/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.rec`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv`.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`. -/
def recEmptyOption {P : (α : Type u) → [FinEnum α] → Sort v}
    (of_equiv : {α β : Type u} → [FinEnum α] → [FinEnum β] → α ≃ β → P α → P β)
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α))
    (α : Type u) [FinEnum α] :
    P α := by
  generalize cardeq : ‹FinEnum α›.card = card
  induction card generalizing α
  case zero =>
    have fzeroeq := Equiv.trans Equiv.ulift.{u} <| cardeq ▸ equiv.symm
    have emptyeq := Equiv.trans Equiv.ulift <| Equiv.equivOfIsEmpty (Fin Nat.zero) PEmpty.{u+1}
    have fzerofe := FinEnum.ofEquiv _ emptyeq
    exact of_equiv fzeroeq <| of_equiv emptyeq.symm h_empty
  case succ n ih _ =>
    have ⟨fe, fecardeq⟩ : { e : _ // e.card = n } := ⟨FinEnum.mk n Equiv.ulift.{u}, rfl⟩
    have fsucceq := Equiv.trans Equiv.ulift.{u} <| cardeq ▸ equiv.symm
    have optioeq :=
      Equiv.trans
        Equiv.ulift <|
        Equiv.trans (@finSuccEquivLast n) <| Equiv.optionCongr Equiv.ulift.symm
    have opsumeq := Equiv.optionEquivSumPUnit.{u,u} <| ULift (Fin n)
    have fssumeq := Equiv.trans optioeq opsumeq
    have fssumfe := @FinEnum.sum _ _ fe FinEnum.punit.{u}
    have fsuccfe := FinEnum.ofEquiv _ fssumeq
    exact of_equiv fsucceq <| of_equiv optioeq.symm <| h_option <| @ih _ fe fecardeq

/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.recOn`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv`.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`. -/
def recOnEmptyOption {P : (α : Type u) → [FinEnum α] → Sort v}
    {α : Type u} (aenum : FinEnum α)
    (of_equiv : {α β : Type u} → [FinEnum α] → [FinEnum β] → α ≃ β → P α → P β)
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α)) :
    P α := @recEmptyOption P of_equiv h_empty h_option α aenum
end FinEnum
