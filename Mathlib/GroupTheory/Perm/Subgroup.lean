/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.GroupTheory.Perm.Basic

#align_import group_theory.perm.subgroup from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `Subgroup`s that exist within `Equiv.Perm α`.
`GroupTheory.Subgroup` depends on `GroupTheory.Perm.Basic`, so these need to be in a separate
file.

It also provides decidable instances on membership in these subgroups, since
`MonoidHom.decidableMemRange` cannot be inferred without the help of a lambda.
The presence of these instances induces a `Fintype` instance on the `QuotientGroup.Quotient` of
these subgroups.
-/


namespace Equiv

namespace Perm

universe u

instance sumCongrHom.decidableMemRange {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] : DecidablePred (· ∈ (sumCongrHom α β).range) := fun _ => inferInstance
#align equiv.perm.sum_congr_hom.decidable_mem_range Equiv.Perm.sumCongrHom.decidableMemRange

@[simp]
theorem sumCongrHom.card_range {α β : Type*} [Fintype (sumCongrHom α β).range]
    [Fintype (Perm α × Perm β)] :
    Fintype.card (sumCongrHom α β).range = Fintype.card (Perm α × Perm β) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sumCongrHom α β) sumCongrHom_injective).symm⟩
#align equiv.perm.sum_congr_hom.card_range Equiv.Perm.sumCongrHom.card_range

instance sigmaCongrRightHom.decidableMemRange {α : Type*} {β : α → Type*} [DecidableEq α]
    [∀ a, DecidableEq (β a)] [Fintype α] [∀ a, Fintype (β a)] :
    DecidablePred (· ∈ (sigmaCongrRightHom β).range) := fun _ => inferInstance
#align equiv.perm.sigma_congr_right_hom.decidable_mem_range Equiv.Perm.sigmaCongrRightHom.decidableMemRange

@[simp]
theorem sigmaCongrRightHom.card_range {α : Type*} {β : α → Type*}
    [Fintype (sigmaCongrRightHom β).range] [Fintype (∀ a, Perm (β a))] :
    Fintype.card (sigmaCongrRightHom β).range = Fintype.card (∀ a, Perm (β a)) :=
  Fintype.card_eq.mpr ⟨(ofInjective (sigmaCongrRightHom β) sigmaCongrRightHom_injective).symm⟩
#align equiv.perm.sigma_congr_right_hom.card_range Equiv.Perm.sigmaCongrRightHom.card_range

instance subtypeCongrHom.decidableMemRange {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (Perm { a // p a } × Perm { a // ¬p a })] [DecidableEq (Perm α)] :
    DecidablePred (· ∈ (subtypeCongrHom p).range) := fun _ => inferInstance
#align equiv.perm.subtype_congr_hom.decidable_mem_range Equiv.Perm.subtypeCongrHom.decidableMemRange

@[simp]
theorem subtypeCongrHom.card_range {α : Type*} (p : α → Prop) [DecidablePred p]
    [Fintype (subtypeCongrHom p).range] [Fintype (Perm { a // p a } × Perm { a // ¬p a })] :
    Fintype.card (subtypeCongrHom p).range =
      Fintype.card (Perm { a // p a } × Perm { a // ¬p a }) :=
  Fintype.card_eq.mpr ⟨(ofInjective (subtypeCongrHom p) (subtypeCongrHom_injective p)).symm⟩
#align equiv.perm.subtype_congr_hom.card_range Equiv.Perm.subtypeCongrHom.card_range

/-- **Cayley's theorem**: Every group G is isomorphic to a subgroup of the symmetric group acting on
`G`. Note that we generalize this to an arbitrary "faithful" group action by `G`. Setting `H = G`
recovers the usual statement of Cayley's theorem via `RightCancelMonoid.faithfulSMul` -/
noncomputable def subgroupOfMulAction (G H : Type*) [Group G] [MulAction G H] [FaithfulSMul G H] :
    G ≃* (MulAction.toPermHom G H).range :=
  MulEquiv.ofLeftInverse' _ (Classical.choose_spec MulAction.toPerm_injective.hasLeftInverse)
#align equiv.perm.subgroup_of_mul_action Equiv.Perm.subgroupOfMulAction

end Perm

end Equiv
