/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# The set of non-invertible elements of a monoid

## Main definitions

* `nonunits` is the set of non-invertible elements of a monoid.

## Main results

* `exists_max_ideal_of_mem_nonunits`: every element of `nonunits` is contained in a maximal ideal
-/

@[expose] public section


variable {F α β : Type*} {a b : α}

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type*) [Monoid α] : Set α :=
  { a | ¬IsUnit a }

@[simp]
theorem mem_nonunits_iff [Monoid α] : a ∈ nonunits α ↔ ¬IsUnit a :=
  Iff.rfl

theorem mul_mem_nonunits_right [CommMonoid α] : b ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_right

theorem mul_mem_nonunits_left [CommMonoid α] : a ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_left

theorem zero_mem_nonunits [MonoidWithZero α] : 0 ∈ nonunits α ↔ (0 : α) ≠ 1 :=
  not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma
theorem one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one

@[deprecated (since := "2025-05-23")] alias one_not_mem_nonunits := one_notMem_nonunits

@[simp high] -- High priority shortcut lemma
theorem map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
    [IsLocalHom f] (a) : f a ∈ nonunits β ↔ a ∈ nonunits α :=
  ⟨fun h ha => h <| ha.map f, fun h ha => h <| ha.of_map⟩

theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I ≠ ⊤) : (I : Set α) ⊆ nonunits α :=
  fun _x hx hu => h <| I.eq_top_of_isUnit_mem hx hu

theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a ∈ nonunits α) :
    ∃ I : Ideal α, I.IsMaximal ∧ a ∈ I := by
  have : Ideal.span ({a} : Set α) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

namespace Submonoid

variable {C : Type*} [SetLike C α]

theorem inv_mem_of_isUnit [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a) :
    (a : α)⁻¹ ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  convert u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

section Group

variable [Group α] [SubmonoidClass C α] {S : C} {a : S}

theorem isUnit_iff : IsUnit a ↔ (a : α)⁻¹ ∈ S where
  mp := inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩

protected theorem mem_nonunits_iff : a ∈ nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff]

end Group

section GroupWithZero

variable [GroupWithZero α] [SubmonoidClass C α] {S : C} {a : S}

theorem isUnit_iff_and : IsUnit a ↔ (a : α) ≠ 0 ∧ (a : α)⁻¹ ∈ S where
  mp h := ⟨(h.map <| subtype <| ofClass S).ne_zero, inv_mem_of_isUnit h⟩
  mpr h :=
    ⟨⟨a, ⟨_, h.2⟩, Subtype.ext (mul_inv_cancel₀ h.1), Subtype.ext (inv_mul_cancel₀ h.1)⟩, rfl⟩

theorem isUnit_iff_of_ne_zero (ha : (a : α) ≠ 0) : IsUnit a ↔ (a : α)⁻¹ ∈ S := by
  rw [isUnit_iff_and, and_iff_right ha]

theorem mem_nonunits_iff_or : a ∈ nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff_and, not_and_or, Ne, not_not]

theorem mem_nonunits_iff_of_ne_zero (ha : (a : α) ≠ 0) : a ∈ nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff_or, or_iff_right ha]

end GroupWithZero

end Submonoid
