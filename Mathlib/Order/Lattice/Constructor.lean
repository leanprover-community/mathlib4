/-
Copyright (c) 2026 Aaron Liu, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Junyan Xu
-/
module

public import Mathlib.Order.Lattice

import Mathlib.Tactic.Order

/-!
# Constructors for distributive and modular lattices

This file provides some constructors for `DistribLattice` with weaker conditions to verify,
using the `order` tactic to facilitate proofs. It also proves an equivalent condition for
`IsModularLattice`, which can be used as a constructor.
-/

public section

theorem isModularLattice_iff_eq_of_le_of_inf_le_of_le_sup {α : Type*} [Lattice α] :
    IsModularLattice α ↔ ∀ x y z : α, x ≤ y → y ⊓ z ≤ x → y ≤ x ⊔ z → x = y :=
  ⟨@eq_of_le_of_inf_le_of_le_sup α _, fun h ↦
    ⟨fun {x} y {z} _ ↦ (h _ _ y (by order) (by order) (by order)).ge⟩⟩

namespace DistribLattice

variable (α : Type*) [Lattice α]

/-- A lattice `α` satisfying `(a ⊔ b) ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c) ⊔ (b ⊓ c)` for all
`a b c : α` is distributive. -/
abbrev ofInfSupLeSupInf (h : ∀ a b c : α, (a ⊔ b) ⊓ (a ⊔ c) ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c ⊔ b ⊓ c) :
    DistribLattice α where
  le_sup_inf := by
    suffices h : ∀ x y z : α, x ⊔ (x ⊔ y) ⊓ (x ⊔ z) ⊓ (y ⊔ z) = (x ⊔ y) ⊓ (x ⊔ z) → _
      from fun x y z ↦ Eq.ge (h x y z ?_)
    on_goal 1 => rw [← inf_comm, h x (y ⊔ z) _ (by order)]
    on_goal 2 => intro x y z; specialize h x y z
    all_goals order

/-- A lattice `α` satisfying the cancellation law `b ⊓ a = c ⊓ a → b ⊔ a = c ⊔ a → b = c` for all
`a b c : α` is distributive. -/
abbrev ofEqOfInfSupEq (h : ∀ a b c : α, a ⊓ b = a ⊓ c → a ⊔ b = a ⊔ c → b = c) :
    DistribLattice α :=
  .ofInfSupLeSupInf α fun a b c ↦
    have : IsModularLattice α :=
      isModularLattice_iff_eq_of_le_of_inf_le_of_le_sup.2
        fun x y z _ _ _ ↦ h z x y (by order) (by order)
    let u (i j k : α) := i ⊓ (j ⊔ k) ⊔ (j ⊓ k)
    let is (i j k : α) := (i ⊔ j) ⊓ (i ⊔ k) ⊓ (j ⊔ k)
    let si (i j k : α) := (i ⊓ j) ⊔ (i ⊓ k) ⊔ (j ⊓ k)
    have u_eq i j k : u i j k = (i ⊔ (j ⊓ k)) ⊓ (j ⊔ k) := by
      unfold u; rw [inf_comm, inf_sup_assoc_of_le _ (by order), inf_comm]
    have u_inf_u i j k : u i j k ⊓ u j i k = si i j k := by
      unfold u si
      rw [← inf_sup_assoc_of_le _ (by order),
        ← sup_comm (j ⊓ k), sup_inf_assoc_of_le _ (by order)]
      order
    have u_sup_u i j k : u i j k ⊔ u j i k = is i j k := by
      unfold is
      rw [u_eq, u_eq, ← sup_inf_assoc_of_le _ (by order),
        ← inf_comm (j ⊔ k), inf_sup_assoc_of_le _ (by order)]
      order
    have u₂₃ i j k : u i j k = u i k j := by unfold u; order
    have u₁₂ i j k : u i j k = u j i k := h (u k i j) _ _
      (by rw [u₂₃ i, u_inf_u, u₂₃, u₂₃ j, u_inf_u]; unfold si; order)
      (by rw [u₂₃ i, u_sup_u, u₂₃, u₂₃ j, u_sup_u]; unfold is; order)
    show is a b c ≤ si a b c by simp [← u_inf_u, ← u_sup_u, u₁₂]

end DistribLattice

end
