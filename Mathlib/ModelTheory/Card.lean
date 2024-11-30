/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of a first-order language

-/

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


namespace Language

variable (L : Language.{u, v})

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
  #L.Symbols

variable {L} {L' : Language.{u', v'}}

theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} #(L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} #(L.Relations l) := by
  simp only [card, mk_sum, mk_sigma, lift_sum]

@[simp]
theorem empty_card : Language.empty.card = 0 := by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]

instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σl, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]
theorem card_functions_sum (i : ℕ) :
    #((L.sum L').Functions i)
      = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal) := by
  simp [Language.sum]

@[simp]
theorem card_relations_sum (i : ℕ) :
    #((L.sum L').Relations i) =
      Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i) := by
  simp [Language.sum]

theorem card_sum :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

variable (L) (M : Type w)
variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

section Empty

variable [Language.empty.Structure M] [Language.empty.Structure N]

@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} #M ≤ Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} #M = Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

end Empty

end Language

end FirstOrder
