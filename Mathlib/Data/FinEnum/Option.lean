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

/-- Inserting an `Option.none` anywhere in an enumeration yields another enumeration. -/
def insertNone (α : Type u) [FinEnum α] (i : Fin (card α + 1)) : FinEnum (Option α) where
  card := card α + 1
  equiv := equiv.optionCongr.trans <| finSuccEquiv' i |>.symm

/-- This is an arbitrary choice of insertion rank for a default instance.
It keeps the mapping of the existing `α`-inhabitants intact, modulo `Fin.castSucc`. -/
instance instFinEnumOptionLast (α : Type u) [FinEnum α] : FinEnum (Option α) :=
  insertNone α (Fin.last <| card α)

/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.rec`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`.
Also, since order matters, the choice of element that gets replaced by `Option.none` has
to be provided for every step.

Since every `FinEnum` instance implies a `Fintype` instance and `Prop` is squashed already,
`Fintype.induction_empty_option` can be used if a `Prop` needs to be constructed.
Cf. `Data.Fintype.Option`
-/
def recEmptyOption {P : (α : Type u) → Sort v}
    (fin_choice : (n : ℕ) → Fin (n + 1))
    (of_equiv : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β )
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α))
    (α : Type u) [FinEnum α] :
    P α :=
  match cardeq : card α with
  | 0 => of_equiv _ _ cardeq h_empty
  | n + 1 =>
    have := uliftId (α := Fin n)
    have : card (ULift.{u} <| Fin n) = n := card_ulift.trans card_fin
    of_equiv (insertNone _ <| fin_choice n) _
      (cardeq.trans <| congrArg Nat.succ this.symm) <|
        h_option (recEmptyOption fin_choice of_equiv h_empty h_option _)
termination_by card α

/--
For a type whose `card` disappears, the recursion principle evaluates to whatever `of_equiv`
makes of the base case.
-/
theorem recEmptyOption_of_card_eq_zero {P : (α : Type u) → Sort v}
    (fin_choice : (n : ℕ) → Fin (n + 1))
    (of_equiv : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β )
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α))
    (α : Type u) [FinEnum α] [fe : FinEnum PEmpty.{u + 1}] (h : card α = 0) :
    recEmptyOption fin_choice of_equiv h_empty h_option α =
      of_equiv _ _ (h.trans <| card_eq_zero_of_IsEmpty _ |>.symm) h_empty := by
  unfold recEmptyOption
  split
  · congr 1; exact Subsingleton.allEq _ _
  · exact Nat.noConfusion <| h.symm.trans ‹_›

/--
For a type whose `card` has a predecessor `n`, the recursion principle evaluates to whatever
`of_equiv` makes of the step result, where `Option.none` has been inserted into the
`(fin_choice n)`th rank of the enumeration.
-/
theorem recEmptyOption_of_card_eq_succ {P : (α : Type u) → Sort v}
    (fin_choice : (n : ℕ) → Fin (n + 1))
    (of_equiv : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β )
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α))
    (α : Type u) [FinEnum α] (n : {n : ℕ // card α = n + 1}) :
    recEmptyOption fin_choice of_equiv h_empty h_option α =
      of_equiv (insertNone _ <| fin_choice n) _
        (n.prop.trans <| congrArg Nat.succ (card_ulift.trans card_fin).symm)
        (h_option
          (recEmptyOption fin_choice of_equiv h_empty h_option (ULift.{u} <| Fin n))) := by
  conv => lhs; unfold recEmptyOption
  split
  · exact Nat.noConfusion <| n.prop.symm.trans ‹_›
  · rcases Nat.succ.inj (n.prop.symm.trans ‹_›) with ⟨rfl⟩; rfl

/-- A recursor principle for finite-and-enumerable types, analogous to `Nat.recOn`.
It effectively says that every `FinEnum` is either `Empty` or `Option α`, up to an `Equiv` mediated
by `Fin`s of equal cardinality.
In contrast to the `Fintype` case, data can be transported along such an `Equiv`.
Also, since order matters, the choice of element that gets replaced by `Option.none` has
to be provided for every step.
-/
abbrev recOnEmptyOption {P : (α : Type u) → Sort v}
    {α : Type u} (aenum : FinEnum α)
    (fin_choice : (n : ℕ) → Fin (n + 1))
    (of_equiv : {α β : Type u} → (_ : FinEnum α) → (_ : FinEnum β) → card β = card α → P α → P β )
    (h_empty : P PEmpty.{u + 1})
    (h_option : {α : Type u} → [FinEnum α] → P α → P (Option α)) :
    P α :=
  @recEmptyOption P fin_choice of_equiv h_empty h_option α aenum

end FinEnum
