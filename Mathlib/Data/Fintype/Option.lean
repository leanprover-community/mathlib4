/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# fintype instances for option
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

open Function

open Nat

universe u v

variable {α β : Type*}

open Finset

instance {α : Type*} [Fintype α] : Fintype (Option α) :=
  ⟨Finset.insertNone univ, fun a => by simp⟩

instance {α : Type*} [Finite α] : Finite (Option α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

theorem univ_option (α : Type*) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl

@[simp]
theorem Fintype.card_option {α : Type*} [Fintype α] :
    Fintype.card (Option α) = Fintype.card α + 1 :=
  (Finset.card_cons (by simp)).trans <| congr_arg₂ _ (card_map _) rfl

/-- If `Option α` is a `Fintype` then so is `α` -/
@[implicit_reducible]
def fintypeOfOption {α : Type*} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (α := Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩

/-- A type is a `Fintype` if its successor (using `Option`) is a `Fintype`. -/
@[implicit_reducible]
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β :=
  haveI := Fintype.ofEquiv _ f
  fintypeOfOption

namespace Fintype

/-- A recursor principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
def truncRecEmptyOption {P : Type u → Sort v} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α] [DecidableEq α], P α → P (Option α))
    (α : Type u) [Fintype α] [DecidableEq α] : Trunc (P α) := by
  suffices ∀ n : ℕ, Trunc (P (ULift <| Fin n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (Equiv.ulift.trans e.symm) h
  intro n
  induction n with
  | zero =>
    have : card PEmpty = card (ULift (Fin 0)) := by
      simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    exact of_equiv e h_empty
  | succ n ih =>
    have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    exact of_equiv e (h_option ih)

/-- An induction principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
@[elab_as_elim]
theorem induction_empty_option {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›)
    (h_empty : P PEmpty) (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u)
    [h_fintype : Fintype α] : P α := by
  obtain ⟨p⟩ :=
    let f_empty := fun i => by convert h_empty
    let h_option : ∀ {α : Type u} [Fintype α] [DecidableEq α],
          (∀ (h : Fintype α), P α) → ∀ (h : Fintype (Option α)), P (Option α) := by
      rintro α hα - Pα hα'
      convert h_option α (Pα _)
    @truncRecEmptyOption (fun α => ∀ h, @P α h) (@fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      f_empty h_option α _ (Classical.decEq α)
  exact p _
  -- ·

end Fintype

/-- An induction principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
theorem Finite.induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u)
    [Finite α] : P α := by
  cases nonempty_fintype α
  refine Fintype.induction_empty_option ?_ ?_ ?_ α
  exacts [fun α β _ => of_equiv, h_empty, @h_option]
