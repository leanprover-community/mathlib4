/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.BooleanAlgebra

#align_import order.heyting.boundary from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Co-Heyting boundary

The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with
itself. The boundary in the co-Heyting algebra of closed sets coincides with the topological
boundary.

## Main declarations

* `Coheyting.boundary`: Co-Heyting boundary. `Coheyting.boundary a = a ⊓ ￢a`

## Notation

`∂ a` is notation for `Coheyting.boundary a` in locale `Heyting`.
-/


variable {α : Type*}

namespace Coheyting

variable [CoheytingAlgebra α] {a b : α}

/-- The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation
with itself. Note that this is always `⊥` for a boolean algebra. -/
def boundary (a : α) : α :=
  a ⊓ ￢a
#align coheyting.boundary Coheyting.boundary

/-- The boundary of an element of a co-Heyting algebra. -/
scoped[Heyting] prefix:120 "∂ " => Coheyting.boundary
-- Porting note: Should the notation be automatically included in the current scope?
open Heyting

-- Porting note: Should hnot be named hNot?
theorem inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a :=
  rfl
#align coheyting.inf_hnot_self Coheyting.inf_hnot_self

theorem boundary_le : ∂ a ≤ a :=
  inf_le_left
#align coheyting.boundary_le Coheyting.boundary_le

theorem boundary_le_hnot : ∂ a ≤ ￢a :=
  inf_le_right
#align coheyting.boundary_le_hnot Coheyting.boundary_le_hnot

@[simp]
theorem boundary_bot : ∂ (⊥ : α) = ⊥ :=
  bot_inf_eq
#align coheyting.boundary_bot Coheyting.boundary_bot

@[simp]
theorem boundary_top : ∂ (⊤ : α) = ⊥ := by rw [boundary, hnot_top, inf_bot_eq]
                                           -- 🎉 no goals
#align coheyting.boundary_top Coheyting.boundary_top

theorem boundary_hnot_le (a : α) : ∂ (￢a) ≤ ∂ a :=
  inf_comm.trans_le <| inf_le_inf_right _ hnot_hnot_le
#align coheyting.boundary_hnot_le Coheyting.boundary_hnot_le

@[simp]
theorem boundary_hnot_hnot (a : α) : ∂ (￢￢a) = ∂ (￢a) := by
  simp_rw [boundary, hnot_hnot_hnot, inf_comm]
  -- 🎉 no goals
#align coheyting.boundary_hnot_hnot Coheyting.boundary_hnot_hnot

@[simp]
theorem hnot_boundary (a : α) : ￢∂ a = ⊤ := by rw [boundary, hnot_inf_distrib, sup_hnot_self]
                                               -- 🎉 no goals
#align coheyting.hnot_boundary Coheyting.hnot_boundary

/-- **Leibniz rule** for the co-Heyting boundary. -/
theorem boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b := by
  unfold boundary
  -- ⊢ a ⊓ b ⊓ ￢(a ⊓ b) = a ⊓ ￢a ⊓ b ⊔ a ⊓ (b ⊓ ￢b)
  rw [hnot_inf_distrib, inf_sup_left, inf_right_comm, ← inf_assoc]
  -- 🎉 no goals
#align coheyting.boundary_inf Coheyting.boundary_inf

theorem boundary_inf_le : ∂ (a ⊓ b) ≤ ∂ a ⊔ ∂ b :=
  (boundary_inf _ _).trans_le <| sup_le_sup inf_le_left inf_le_right
#align coheyting.boundary_inf_le Coheyting.boundary_inf_le

theorem boundary_sup_le : ∂ (a ⊔ b) ≤ ∂ a ⊔ ∂ b := by
  rw [boundary, inf_sup_right]
  -- ⊢ a ⊓ ￢(a ⊔ b) ⊔ b ⊓ ￢(a ⊔ b) ≤ ∂ a ⊔ ∂ b
  exact
    sup_le_sup (inf_le_inf_left _ <| hnot_anti le_sup_left)
      (inf_le_inf_left _ <| hnot_anti le_sup_right)
#align coheyting.boundary_sup_le Coheyting.boundary_sup_le

/- The intuitionistic version of `Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`. Either
proof can be obtained from the other using the equivalence of Heyting algebras and intuitionistic
logic and duality between Heyting and co-Heyting algebras. It is crucial that the following proof be
intuitionistic. -/
example (a b : Prop) : (a ∧ b ∨ ¬(a ∧ b)) ∧ ((a ∨ b) ∨ ¬(a ∨ b)) → a ∨ ¬a := by
  rintro ⟨⟨ha, _⟩ | hnab, (ha | hb) | hnab⟩ <;> try exact Or.inl ha
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- ⊢ a ∨ ¬a
                                                -- ⊢ a ∨ ¬a
  · exact Or.inr fun ha => hnab ⟨ha, hb⟩
    -- 🎉 no goals
  · exact Or.inr fun ha => hnab <| Or.inl ha
    -- 🎉 no goals

theorem boundary_le_boundary_sup_sup_boundary_inf_left : ∂ a ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  -- Porting note: the following simp generates the same term as mathlib3 if you remove
  -- sup_inf_right from both. With sup_inf_right included, mathlib4 and mathlib3 generate
  -- different terms
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    @sup_comm _ _ _ a]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> try { exact le_sup_of_le_left inf_le_left } <;>
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- ⊢ a ⊓ ￢a ≤ ￢(a ⊔ b) ⊔ b
                                            -- 🎉 no goals
                                            -- ⊢ a ⊓ ￢a ≤ ￢(a ⊔ b) ⊔ ￢(a ⊓ b)
    refine inf_le_of_right_le ?_
    -- ⊢ ￢a ≤ ￢(a ⊔ b) ⊔ b
    -- ⊢ ￢a ≤ ￢(a ⊔ b) ⊔ ￢(a ⊓ b)
  · rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm]
    -- ⊢ Codisjoint (￢(a ⊔ b)) (a ⊔ b)
    exact codisjoint_hnot_left
    -- 🎉 no goals
  · refine le_sup_of_le_right ?_
    -- ⊢ ￢a ≤ ￢(a ⊓ b)
    rw [hnot_le_iff_codisjoint_right]
    -- ⊢ Codisjoint a (￢(a ⊓ b))
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left)
    -- 🎉 no goals
#align coheyting.boundary_le_boundary_sup_sup_boundary_inf_left Coheyting.boundary_le_boundary_sup_sup_boundary_inf_left

theorem boundary_le_boundary_sup_sup_boundary_inf_right : ∂ b ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) := by
  rw [@sup_comm _ _ a, inf_comm]
  -- ⊢ ∂ b ≤ ∂ (b ⊔ a) ⊔ ∂ (b ⊓ a)
  exact boundary_le_boundary_sup_sup_boundary_inf_left
  -- 🎉 no goals
#align coheyting.boundary_le_boundary_sup_sup_boundary_inf_right Coheyting.boundary_le_boundary_sup_sup_boundary_inf_right

theorem boundary_sup_sup_boundary_inf (a b : α) : ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b :=
  le_antisymm (sup_le boundary_sup_le boundary_inf_le) <|
    sup_le boundary_le_boundary_sup_sup_boundary_inf_left
      boundary_le_boundary_sup_sup_boundary_inf_right
#align coheyting.boundary_sup_sup_boundary_inf Coheyting.boundary_sup_sup_boundary_inf

@[simp]
theorem boundary_idem (a : α) : ∂ ∂ a = ∂ a := by rw [boundary, hnot_boundary, inf_top_eq]
                                                  -- 🎉 no goals
#align coheyting.boundary_idem Coheyting.boundary_idem

theorem hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔ ∂ a = a := by
  rw [boundary, sup_inf_left, hnot_sup_self, inf_top_eq, sup_eq_right]
  -- ⊢ ￢￢a ≤ a
  exact hnot_hnot_le
  -- 🎉 no goals
#align coheyting.hnot_hnot_sup_boundary Coheyting.hnot_hnot_sup_boundary

theorem hnot_eq_top_iff_exists_boundary : ￢a = ⊤ ↔ ∃ b, ∂ b = a :=
  ⟨fun h => ⟨a, by rw [boundary, h, inf_top_eq]⟩, by
                   -- 🎉 no goals
    rintro ⟨b, rfl⟩
    -- ⊢ ￢∂ b = ⊤
    exact hnot_boundary _⟩
    -- 🎉 no goals
#align coheyting.hnot_eq_top_iff_exists_boundary Coheyting.hnot_eq_top_iff_exists_boundary

end Coheyting

open Heyting

section BooleanAlgebra

variable [BooleanAlgebra α]

@[simp]
theorem Coheyting.boundary_eq_bot (a : α) : ∂ a = ⊥ :=
  inf_compl_eq_bot
#align coheyting.boundary_eq_bot Coheyting.boundary_eq_bot

end BooleanAlgebra
