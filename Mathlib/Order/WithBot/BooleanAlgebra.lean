/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.WithBot.Basic

/-!
## `WithTop`/`WithBot` and the `BooleanAlgebra` structure on `Set`
-/

open Function Set
theorem Set.isCompl_range_coe_bot (α : Type*) :
    IsCompl (range ((↑) : α → WithBot α)) {⊥} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, hn⟩ => WithBot.coe_ne_bot <| ha.trans <| eq_of_mem_singleton hn)
    fun x _ => x.recBotCoe (Or.inr <| mem_singleton _) fun _ => Or.inl <| mem_range_self _

theorem Set.isCompl_range_coe_top (α : Type*) :
    IsCompl (range ((↑) : α → WithTop α)) {⊤} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, hn⟩ => WithTop.coe_ne_top <| ha.trans <| eq_of_mem_singleton hn)
    fun x _ => x.recTopCoe (Or.inr <| mem_singleton _) fun _ => Or.inl <| mem_range_self _
