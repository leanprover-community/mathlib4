/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathlib.Computability.Encoding.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Inequalities on cardinalities implied by encodings
-/


universe u v

open Cardinal

namespace Computability

theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} #α ≤ Cardinal.lift.{u} #(List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩

theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Countable e.Γ] :
    #α ≤ ℵ₀ :=
  haveI : Countable α := e.encode_injective.countable
  Cardinal.mk_le_aleph0

theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : #α ≤ ℵ₀ :=
  e.toEncoding.card_le_aleph0

end Computability
