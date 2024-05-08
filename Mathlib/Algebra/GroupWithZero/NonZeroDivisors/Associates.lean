/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors.Basic

/-!
# Associates and non zero divisors

In this file, we prove results relating the associates relation and the non-zero-divisors of a
`MonoidWithZero`.

## Main results

* `nonZeroDivisorsUnitsEquiv`: The units of the monoid of non-zero-divisors of a
`MonoidWithZero` are equivalent to the units of `α`

* `AssociatesNonZeroDivisorsMulEquiv`: the `MulEquiv` between `Associates α⁰ ≃* (Associates α)⁰`
where `α` is a `CommMonoidWithZero`.

-/

noncomputable section

open nonZeroDivisors

/-- The units of the monoid of non zero divisors of `α` are equivalent to the units of `α`. -/
def nonZeroDivisorsUnitsEquiv (α : Type*) [MonoidWithZero α] :
    (α⁰)ˣ ≃* αˣ :=
  MulEquiv.ofBijective (Units.map α⁰.subtype) ⟨Units.map_injective Subtype.val_injective,
    fun u ↦ ⟨IsUnit.unit ⟨⟨⟨u, IsUnit.mem_nonZeroDivisors u.isUnit⟩, ⟨(u⁻¹ : αˣ),
        IsUnit.mem_nonZeroDivisors u⁻¹.isUnit⟩, by simp, by simp⟩, rfl⟩,
      by rw [Units.ext_iff, IsUnit.unit_of_val_units, Units.coe_map, Submonoid.coe_subtype]⟩⟩

@[simp]
theorem nonZeroDivisorsUnitsEquiv_apply (α : Type*) [MonoidWithZero α] (u : (α⁰)ˣ) :
    nonZeroDivisorsUnitsEquiv α u = (u : α) := rfl

@[simp]
theorem nonZeroDivisorsUnitsEquiv_symm_apply (α : Type*) [MonoidWithZero α] (u : αˣ) :
    ((nonZeroDivisorsUnitsEquiv α).symm u : α) = (u : α) := by
  obtain ⟨v, rfl⟩ := (nonZeroDivisorsUnitsEquiv α).surjective u
  rw [MulEquiv.symm_apply_apply, nonZeroDivisorsUnitsEquiv_apply]

theorem Associates_mk_mem_nonZeroDivisors_iff {α : Type*} [CommMonoidWithZero α] (a : α) :
    Associates.mk a ∈ (Associates α)⁰ ↔ a ∈ α⁰ := by
  rw [mem_nonZeroDivisors_iff, mem_nonZeroDivisors_iff, ← not_iff_not]
  push_neg
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

/-- To any class in `Associates α⁰`, one can associate a class in `(Associates α)⁰` by sending a
representative `a : α⁰` of the class to the class of `(a : α)`. The map obtained is in fact a
`MulEquiv`, see `AssociatesNonZeroDivisorsMulEquiv`. -/
def AssociatesNonZeroDivisorsMonoidHom (α : Type*) [CommMonoidWithZero α] :
    Associates α⁰ →* (Associates α)⁰ where
  toFun := Quotient.lift (fun ⟨x, _⟩ ↦  ⟨Associates.mk x, by
      rwa [Associates_mk_mem_nonZeroDivisors_iff]⟩) (by
    rintro _ _ ⟨v, hv⟩
    rw [Subtype.mk.injEq, Associates.mk_eq_mk_iff_associated]
    exact ⟨nonZeroDivisorsUnitsEquiv α v, by
      rw [nonZeroDivisorsUnitsEquiv_apply, ← hv, Submonoid.coe_mul]⟩)
  map_one' := rfl
  map_mul' x y := Quotient.inductionOn₂ x y fun _ _ ↦ rfl

@[simp]
theorem AssociatesNonZeroDivisorsMonoidHom_apply (α : Type*) [CommMonoidWithZero α] (a : α⁰) :
    (AssociatesNonZeroDivisorsMonoidHom α ⟦a⟧ : Associates α) = Associates.mk (a : α) := rfl

/-- This is the `MulEquiv` version of `AssociatesNonZeroDivisorsMonoidHom`. -/
def AssociatesNonZeroDivisorsMulEquiv (α : Type*) [CommMonoidWithZero α] :
    Associates α⁰ ≃* (Associates α)⁰  := by
  refine MulEquiv.ofBijective (AssociatesNonZeroDivisorsMonoidHom α) ⟨?_, ?_⟩
  · rintro ⟨_⟩ ⟨_⟩ h
    rw [Subtype.ext_iff, Associates.quot_mk_eq_mk, Associates.quot_mk_eq_mk,
      AssociatesNonZeroDivisorsMonoidHom_apply, AssociatesNonZeroDivisorsMonoidHom_apply] at h
    obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp h
    rw [Associates.quot_mk_eq_mk, Associates.quot_mk_eq_mk]
    refine Associates.mk_eq_mk_iff_associated.mpr ⟨?_, ?_⟩
    · exact (nonZeroDivisorsUnitsEquiv α).symm u
    · rwa [Subtype.ext_iff, Submonoid.coe_mul, nonZeroDivisorsUnitsEquiv_symm_apply]
  · rintro ⟨⟨y⟩, hy⟩
    refine ⟨⟦⟨y, ?_⟩⟧, ?_⟩
    · rwa [← Associates_mk_mem_nonZeroDivisors_iff, ← Associates.quot_mk_eq_mk]
    · rw [Subtype.ext_iff, AssociatesNonZeroDivisorsMonoidHom_apply, ← Associates.quot_mk_eq_mk]

@[simp]
theorem AssociatesNonZeroDivisorsMulEquiv_apply (α : Type*) [CommMonoidWithZero α] (a : α⁰) :
    (AssociatesNonZeroDivisorsMulEquiv α ⟦a⟧ : Associates α) = Associates.mk (a : α) := rfl
