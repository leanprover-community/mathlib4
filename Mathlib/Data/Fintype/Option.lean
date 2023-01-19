/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.option
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Option

/-!
# fintype instances for option
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

instance {α : Type _} [Fintype α] : Fintype (Option α) :=
  ⟨univ.insertNone, fun a => by simp⟩

theorem univ_option (α : Type _) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl
#align univ_option univ_option

@[simp]
theorem Fintype.card_option {α : Type _} [Fintype α] :
    Fintype.card (Option α) = Fintype.card α + 1 :=
  (Finset.card_cons _).trans <| congr_arg₂ _ (card_map _) rfl
#align fintype.card_option Fintype.card_option

/-- If `option α` is a `fintype` then so is `α` -/
def fintypeOfOption {α : Type _} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩
#align fintype_of_option fintypeOfOption

/-- A type is a `fintype` if its successor (using `option`) is a `fintype`. -/
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β :=
  haveI := Fintype.ofEquiv _ f
  fintypeOfOption
#align fintype_of_option_equiv fintypeOfOptionEquiv

namespace Fintype

/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def truncRecEmptyOption {P : Type u → Sort v} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α] [DecidableEq α], P α → P (Option α))
    (α : Type u) [Fintype α] [DecidableEq α] : Trunc (P α) :=
  by
  suffices ∀ n : ℕ, Trunc (P (ULift <| Fin n))
    by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (equiv.ulift.trans e.symm) h
  intro n
  induction' n with n ih
  · have : card PEmpty = card (ULift (Fin 0)) := by simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (trunc_equiv_of_card_eq this)
    intro e
    apply Trunc.mk
    refine' of_equiv e h_empty
  · have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (trunc_equiv_of_card_eq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    refine' of_equiv e (h_option ih)
#align fintype.trunc_rec_empty_option Fintype.truncRecEmptyOption

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_elim]
theorem induction_empty_option {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›)
    (h_empty : P PEmpty) (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u)
    [Fintype α] : P α :=
  by
  obtain ⟨p⟩ :=
    @trunc_rec_empty_option (fun α => ∀ h, @P α h) (fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      (fun _i => by convert h_empty) _ α _ (Classical.decEq α)
  · exact p _
  · rintro α hα - Pα hα'
    skip
    convert h_option α (Pα _)
#align fintype.induction_empty_option Fintype.induction_empty_option

end Fintype

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
theorem Finite.induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u)
    [Finite α] : P α := by
  cases nonempty_fintype α
  refine' Fintype.induction_empty_option _ _ _ α
  exacts[fun α β _ => of_equiv, h_empty, @h_option]
#align finite.induction_empty_option Finite.induction_empty_option

