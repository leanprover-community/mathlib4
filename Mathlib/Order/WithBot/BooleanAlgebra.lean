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

variable (α : Type*)

namespace Set

section WithBot

theorem isCompl_range_coe_bot : IsCompl (range ((↑) : α → WithBot α)) {⊥} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, hn⟩ => WithBot.coe_ne_bot <| ha.trans <| eq_of_mem_singleton hn)
    fun x _ => x.recBotCoe (Or.inr <| mem_singleton _) fun _ => Or.inl <| mem_range_self _

@[simp]
theorem compl_range_coe_eq_singleton_bot : (range ((↑) : α → WithBot α))ᶜ = {⊥} :=
  (isCompl_range_coe_bot α).compl_eq

@[simp]
theorem range_coe_inter_bot : (range ((↑) : α → WithBot α)) ∩ {⊥} = ∅ :=
  (isCompl_range_coe_bot α).inf_eq_bot

theorem range_coe_union_bot : range ((↑) : α → WithBot α) ∪ {⊥} = univ :=
  (isCompl_range_coe_bot α).sup_eq_top

@[simp]
theorem insert_bot_range_coe : insert ⊥ (range ((↑) : α → WithBot α)) = univ := by
  simpa using range_coe_union_bot α

end WithBot

section WithTop

theorem isCompl_range_coe_top : IsCompl (range ((↑) : α → WithTop α)) {⊤} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, hn⟩ => WithTop.coe_ne_top <| ha.trans <| eq_of_mem_singleton hn)
    fun x _ => x.recTopCoe (Or.inr <| mem_singleton _) fun _ => Or.inl <| mem_range_self _

@[simp]
theorem compl_range_coe_eq_singleton_top : (range ((↑) : α → WithTop α))ᶜ = {⊤} :=
  (isCompl_range_coe_top α).compl_eq

@[simp]
theorem range_coe_inter_top : (range ((↑) : α → WithTop α)) ∩ {⊤} = ∅ :=
  (isCompl_range_coe_top α).inf_eq_bot

theorem range_coe_union_top : range ((↑) : α → WithTop α) ∪ {⊤} = univ :=
  (isCompl_range_coe_top α).sup_eq_top

@[simp]
theorem insert_top_range_coe : insert ⊤ (range ((↑) : α → WithTop α)) = univ := by
  simpa using range_coe_union_top α

end WithTop

end Set
