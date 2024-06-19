/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Regular

#align_import ring_theory.ore_localization.ore_set from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

/-!

# (Right) Ore sets

This defines right Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/


namespace OreLocalization

section Monoid

/-- A submonoid `S` of a monoid `R` is (right) Ore if common factors on the left can be turned
into common factors on the right, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `r * u = s * v`. -/
class OreSet {R : Type*} [Monoid R] (S : Submonoid R) where
  /-- Common factors on the left can be turned into common factors on the right, a weak form of
cancellability. -/
  ore_left_cancel : ∀ (r₁ r₂ : R) (s : S), ↑s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s'
  /-- The Ore numerator of a fraction. -/
  oreNum : R → S → R
  /-- The Ore denominator of a fraction. -/
  oreDenom : R → S → S
  /-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
  ore_eq : ∀ (r : R) (s : S), r * oreDenom r s = s * oreNum r s
#align ore_localization.ore_set OreLocalization.OreSet

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]

/-- Common factors on the left can be turned into common factors on the right, a weak form of
cancellability. -/
theorem ore_left_cancel (r₁ r₂ : R) (s : S) (h : ↑s * r₁ = s * r₂) : ∃ s' : S, r₁ * s' = r₂ * s' :=
  OreSet.ore_left_cancel r₁ r₂ s h
#align ore_localization.ore_left_cancel OreLocalization.ore_left_cancel

/-- The Ore numerator of a fraction. -/
def oreNum (r : R) (s : S) : R :=
  OreSet.oreNum r s
#align ore_localization.ore_num OreLocalization.oreNum

/-- The Ore denominator of a fraction. -/
def oreDenom (r : R) (s : S) : S :=
  OreSet.oreDenom r s
#align ore_localization.ore_denom OreLocalization.oreDenom

/-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
theorem ore_eq (r : R) (s : S) : r * oreDenom r s = s * oreNum r s :=
  OreSet.ore_eq r s
#align ore_localization.ore_eq OreLocalization.ore_eq

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
def oreCondition (r : R) (s : S) : Σ'r' : R, Σ's' : S, r * s' = s * r' :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
#align ore_localization.ore_condition OreLocalization.oreCondition

/-- The trivial submonoid is an Ore set. -/
instance oreSetBot : OreSet (⊥ : Submonoid R) where
  ore_left_cancel _ _ s h :=
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [one_mul, one_mul] at h
      subst h
      rfl⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]
#align ore_localization.ore_set_bot OreLocalization.oreSetBot

/-- Every submonoid of a commutative monoid is an Ore set. -/
instance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where
  ore_left_cancel m n s h := ⟨s, by rw [mul_comm n s, mul_comm m s, h]⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by rw [mul_comm]
#align ore_localization.ore_set_comm OreLocalization.oreSetComm

end Monoid

/-- Cancellability in monoids with zeros can act as a replacement for the `ore_left_cancel`
condition of an ore set. -/
def oreSetOfCancelMonoidWithZero {R : Type*} [CancelMonoidWithZero R] {S : Submonoid R}
    (oreNum : R → S → R) (oreDenom : R → S → S)
    (ore_eq : ∀ (r : R) (s : S), r * oreDenom r s = s * oreNum r s) : OreSet S :=
  { ore_left_cancel := fun _ _ s h => ⟨s, mul_eq_mul_right_iff.mpr (mul_eq_mul_left_iff.mp h)⟩
    oreNum
    oreDenom
    ore_eq }
#align ore_localization.ore_set_of_cancel_monoid_with_zero OreLocalization.oreSetOfCancelMonoidWithZero

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
def oreSetOfNoZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R] {S : Submonoid R}
    (oreNum : R → S → R) (oreDenom : R → S → S)
    (ore_eq : ∀ (r : R) (s : S), r * oreDenom r s = s * oreNum r s) : OreSet S :=
  letI : CancelMonoidWithZero R := NoZeroDivisors.toCancelMonoidWithZero
  oreSetOfCancelMonoidWithZero oreNum oreDenom ore_eq
#align ore_localization.ore_set_of_no_zero_divisors OreLocalization.oreSetOfNoZeroDivisors

lemma nonempty_oreSet_iff {R : Type*} [Ring R] {S : Submonoid R} :
    Nonempty (OreSet S) ↔ (∀ (r₁ r₂ : R) (s : S), ↑s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s') ∧
      (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r') := by
  constructor
  · exact fun ⟨_⟩ ↦ ⟨ore_left_cancel, fun r s ↦ ⟨oreNum r s, oreDenom r s, ore_eq r s⟩⟩
  · intro ⟨H, H'⟩
    choose r' s' h using H'
    exact ⟨H, r', s', h⟩

lemma nonempty_oreSet_iff_of_noZeroDivisors {R : Type*} [Ring R] [NoZeroDivisors R]
    {S : Submonoid R} :
    Nonempty (OreSet S) ↔ ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r' := by
  constructor
  · exact fun ⟨_⟩ ↦ fun r s ↦ ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
  · intro H
    choose r' s' h using H
    exact ⟨oreSetOfNoZeroDivisors r' s' h⟩

end OreLocalization
