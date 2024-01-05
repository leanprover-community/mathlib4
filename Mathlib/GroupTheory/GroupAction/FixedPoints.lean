/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Dynamics.PeriodicPts

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib.GroupTheory.GroupAction.Basic`,
as well as the definition of `MulAction.movedBy`.
-/

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]


section FixedPoints

/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive "In an additive group action, the points fixed by `g` are also fixed by `g⁻¹`"]
theorem fixedBy_eq_fixedBy_inv (g : G) : fixedBy α g = fixedBy α g⁻¹ := by
  ext x
  repeat rw [mem_fixedBy]
  constructor
  all_goals (intro gx_eq_x; nth_rw 1 [<-gx_eq_x])
  · exact inv_smul_smul g x
  · rw [<-mul_smul, mul_right_inv, one_smul]

@[to_additive]
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [mem_fixedBy, smul_left_cancel_iff]
  rfl

@[to_additive]
theorem minimalPeriod_eq_one_of_fixedBy {a : α} {g : G} (a_in_fixedBy : a ∈ fixedBy α g) :
    Function.minimalPeriod (fun x => g • x) a = 1 := by
  rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
  exact a_in_fixedBy

@[to_additive]
theorem fixedBy_subset_fixedBy_pow (g : G) (j : ℤ) :
    fixedBy α g ⊆ fixedBy α (g^j) := by
  intro a a_in_fixedBy
  rw [
    mem_fixedBy,
    zpow_smul_eq_iff_minimalPeriod_dvd,
    minimalPeriod_eq_one_of_fixedBy a_in_fixedBy
  ]
  rw [Nat.cast_one]
  exact one_dvd j

variable (M)

@[to_additive (attr := simp)]
theorem fixedBy_one_eq_univ :
    fixedBy α (1 : M) = Set.univ := by
  ext a
  rw [mem_fixedBy, one_smul]
  exact ⟨fun _ => Set.mem_univ a, fun _ => rfl⟩

end FixedPoints

section MovedBy

variable (α)

/-- The set of points moved by an element of the action. -/
@[to_additive "The set of points moved by an element of the action."]
def movedBy (m : M) : Set α := { a : α | m • a ≠ a }

variable {α}

@[to_additive (attr := simp)]
theorem mem_movedBy {m : M} {a : α} : a ∈ movedBy α m ↔ m • a ≠ a :=
  Iff.rfl

@[to_additive]
theorem movedBy_eq_compl_fixedBy {m : M} : movedBy α m = (fixedBy α m)ᶜ := rfl

@[to_additive]
theorem fixedBy_eq_compl_movedBy {m : M} : fixedBy α m = (movedBy α m)ᶜ := by
  rw [<-compl_compl (fixedBy α m), movedBy_eq_compl_fixedBy]

@[to_additive]
theorem not_mem_fixedBy_iff_mem_movedBy {m : M} {a : α} : a ∉ fixedBy α m ↔ a ∈ movedBy α m :=
  Iff.rfl

@[to_additive]
theorem not_mem_movedBy_iff_mem_fixedBy {m : M} {a : α} : a ∉ movedBy α m ↔ a ∈ fixedBy α m := by
  rw [movedBy_eq_compl_fixedBy, Set.not_mem_compl_iff]

/-- In a multiplicative group action, the points moved by `g` are also moved by `g⁻¹` -/
@[to_additive "In an additive group action, the points moved by `g` are also moved by `g⁻¹`"]
theorem movedBy_eq_movedBy_inv (g : G) : movedBy α g = movedBy α g⁻¹ := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [fixedBy_eq_fixedBy_inv]

@[to_additive]
theorem smul_mem_movedBy_iff_mem_movedBy {a : α} {g : G} :
    g • a ∈ movedBy α g ↔ a ∈ movedBy α g := by
  repeat rw [<-not_mem_fixedBy_iff_mem_movedBy]
  rw [smul_mem_fixedBy_iff_mem_fixedBy]

@[to_additive]
theorem movedBy_pow_subset_movedBy (g : G) (j : ℤ) :
    movedBy α (g^j) ⊆ movedBy α g := by
  repeat rw [movedBy_eq_compl_fixedBy]
  rw [Set.compl_subset_compl]
  exact fixedBy_subset_fixedBy_pow g j

@[to_additive (attr := simp)]
theorem movedBy_one_eq_empty (α) (M : Type u) [Monoid M] [MulAction M α] :
    movedBy α (1 : M) = ∅ := by
  rw [movedBy_eq_compl_fixedBy, fixedBy_one_eq_univ, Set.compl_univ]

/-- If `s` is a superset of `movedBy α g`, then `g` cannot move a point outside of `s`. -/
@[to_additive "If `s` is a superset of `movedBy α g`, then `g` cannot move a point outside of `s`."]
theorem smul_pow_in_set_of_movedBy_subset {a : α} {s : Set α} {g : G} (s_subset : movedBy α g ⊆ s)
    (j : ℤ) : g^j • a ∈ s ↔ a ∈ s := by
  rcases (Classical.em (a ∈ movedBy α (g^j))) with a_moved | a_fixed
  · constructor
    all_goals (intro; apply s_subset)
    all_goals apply movedBy_pow_subset_movedBy g j
    · exact a_moved
    · rw [smul_mem_movedBy_iff_mem_movedBy]
      exact a_moved
  · rw [not_mem_movedBy_iff_mem_fixedBy, mem_fixedBy] at a_fixed
    rw [a_fixed]

@[to_additive]
theorem smul_in_set_of_movedBy_subset {a : α} {s : Set α} {g : G} (s_subset : movedBy α g ⊆ s) :
    g • a ∈ s ↔ a ∈ s := (zpow_one g) ▸ smul_pow_in_set_of_movedBy_subset s_subset 1

end MovedBy

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the action is faithful, then an empty `movedBy` set implies that `m = 1` -/
@[to_additive]
theorem movedBy_empty_iff_eq_one {m : M} : movedBy α m = ∅ ↔ m = 1 := ⟨
  (by
    intro moved_empty
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro a
    rw [one_smul]
    by_contra ma_ne_a
    rwa [<-ne_eq, <-mem_movedBy, moved_empty] at ma_ne_a
  ),
  fun eq_one => eq_one.symm ▸ movedBy_one_eq_empty α M
⟩

end Faithful

end MulAction
