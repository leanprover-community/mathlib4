/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Action.Opposite

/-!

# (Left) Ore sets

This defines left Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

assert_not_exists RelIso

universe u v

namespace AddOreLocalization

/-- A submonoid `S` of an additive monoid `R` is (left) Ore if common summands on the right can be
turned into common summands on the left, and if each pair of `r : R` and `s : S` admits an Ore
minuend `v : R` and an Ore subtrahend `u : S` such that `u + r = v + s`. -/
class AddOreSet {R : Type u} [AddMonoid R] (S : AddSubmonoid R) (M : Type v)
    [AddAction R M] [AddAction Rᵃᵒᵖ M] where
  /-- Common summands on the right can be turned into common summands on the left, a weak form of
cancellability. -/
  ore_right_cancel :
    ∀ (r₁ r₂ : M) (s : S),
      AddOpposite.op (s : R) +ᵥ r₁ = AddOpposite.op (s : R) +ᵥ r₂ →
        ∃ s' : S, (s' : R) +ᵥ r₁ = (s' : R) +ᵥ r₂
  /-- The Ore minuend of a difference. -/
  oreMin : M → S → M
  /-- The Ore subtrahend of a difference. -/
  oreSubtra : M → S → S
  /-- The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`. -/
  ore_eq : ∀ (r : M) (s : S), (oreSubtra r s : R) +ᵥ r = AddOpposite.op (s : R) +ᵥ (oreMin r s : M)

end AddOreLocalization

namespace OreLocalization

section Monoid

open scoped RightActions


/-- A submonoid `S` of a monoid `R` is (left) Ore if common factors on the right can be turned
into common factors on the left, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `u * r = v * s`. -/
@[to_additive AddOreLocalization.AddOreSet]
class OreSet {R : Type u} [Monoid R] (S : Submonoid R) (M : Type v)
    [MulAction R M] [MulAction Rᵐᵒᵖ M] where
  /-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
  ore_right_cancel :
    ∀ (r₁ r₂ : M) (s : S), r₁ <• (s : R) = r₂ <• (s : R) → ∃ s' : S, (s' : R) • r₁ = (s' : R) • r₂
  /-- The Ore numerator of a fraction. -/
  oreNum : M → S → M
  /-- The Ore denominator of a fraction. -/
  oreDenom : M → S → S
  /-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
  ore_eq : ∀ (r : M) (s : S), (oreDenom r s : R) • r = oreNum r s <• (s : R)

-- TODO: use this once it's available.
-- run_cmd to_additive.map_namespace `OreLocalization `AddOreLocalization

variable {R M: Type*} [Monoid R] [MulAction R M] [MulAction Rᵐᵒᵖ M] {S : Submonoid R} [OreSet S M]

/-- Common factors on the right can be turned into common factors on the left, a weak form of
cancellability. -/
@[to_additive AddOreLocalization.ore_right_cancel]
theorem ore_right_cancel (r₁ r₂ : M) (s : S) (h : r₁ <• (s : R) = r₂ <• (s : R)) :
    ∃ s' : S, (s' : R) • r₁ = (s' : R) • r₂  :=
  OreSet.ore_right_cancel r₁ r₂ s h

/-- The Ore numerator of a fraction. -/
@[to_additive AddOreLocalization.oreMin "The Ore minuend of a difference."]
def oreNum (r : M) (s : S) : M :=
  OreSet.oreNum r s

/-- The Ore denominator of a fraction. -/
@[to_additive AddOreLocalization.oreSubtra "The Ore subtrahend of a difference."]
def oreDenom (r : M) (s : S) : S :=
  OreSet.oreDenom r s

/-- The Ore condition of a fraction, expressed in terms of `oreNum` and `oreDenom`. -/
@[to_additive AddOreLocalization.add_ore_eq
  "The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`."]
theorem ore_eq (r : M) (s : S) : (oreDenom r s : R) • r = oreNum r s <• (s : R) :=
  OreSet.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
@[to_additive AddOreLocalization.addOreCondition
  "The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given difference."]
def oreCondition (r : M) (s : S) : Σ'r' : M, Σ's' : S, (s' : R) • r = r' <• (s : R) :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
@[to_additive AddOreLocalization.addOreSetBot]
instance oreSetBot : OreSet (⊥ : Submonoid R) M where
  ore_right_cancel _ _ s h :=
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      simpa using h⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]

/-- Every submonoid of a commutative monoid is an Ore set. -/
@[to_additive AddOreLocalization.addOreSetComm]
instance (priority := 100) oreSetComm {R} [CommMonoid R] [MulAction R M] [MulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (S : Submonoid R) : OreSet S M where
  ore_right_cancel m n s h := ⟨s, by simpa [op_smul_eq_smul] using h⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by rw [op_smul_eq_smul]

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreMin]
lemma oreSetComm_oreNum {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreNum r s = r := rfl

@[to_additive (attr := simp) AddOreLocalization.addOreSetComm_oreSubtra]
lemma oreSetComm_oreDenom {R : Type*} [CommMonoid R] (S : Submonoid R) (r : R) (s : S) :
    oreDenom r s = s := rfl

end Monoid

end OreLocalization
