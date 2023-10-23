/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Projective Special Linear Group

## Notation

In the `MatrixGroups` locale:

* `PSL(n, R)` is a shorthand for `Matrix.ProjectiveSpecialLinearGroup (Fin n) R`
-/

namespace Matrix

universe u v

open Matrix LinearMap

open scoped MatrixGroups

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- A projective special linear group is the quotient of a special linear group by its center.-/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`.-/
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] [Inhabited n]
    {α : Type*}

namespace SpecialLinearGroup

open SpecialLinearGroup

/-- This is a converter to help you with `quotient.liftOn'` and `quotient.liftOn₂'`.

Example :
```lean
instance : SMul PSL(2, ℝ) ℍ where
  smul g := Quotient.liftOn' g (· • ·) <| by
    intro A B hAB
    rw [@QuotientGroup.leftRel_apply] at hAB
    rw [SpecialLinearGroup.coset_center_iff] at hAB
```
-/
theorem coset_center_iff
    {A B : SpecialLinearGroup n R} : A⁻¹ * B ∈ Subgroup.center (SpecialLinearGroup n R) ↔
    ∃ (c : R), (c ^ Fintype.card n = 1 ∧ B.val = c • A.val) := by
  constructor
  · intro hAB
    obtain ⟨hc, hAB⟩ := mem_center_iff.mp hAB
    set c := (A⁻¹ * B).val default default
    use c
    replace hAB := congrArg (HMul.hMul A.val) hAB
    rw [coe_mul, ← mul_assoc, mul_smul, mul_one, ← coe_mul,
        @mul_inv_self, coe_one, one_mul] at hAB
    exact ⟨hc, hAB⟩
  · intro hc
    choose c hc hAB using hc
    replace hAB := congrArg (HMul.hMul A⁻¹.val) hAB
    rw [@mul_smul, ← coe_mul, ← coe_mul, @mul_left_inv] at hAB
    refine mem_center_iff.mpr ?_
    have : (A⁻¹ * B) default default = c := by
      rw [hAB, @smul_apply]
      simp
    rw [this]
    exact ⟨hc, hAB⟩

section SL2

variable [Fact (Even (Fintype.card n))] {hn : Fintype.card n = 2} [NoZeroDivisors R]

/-- This is a converter to help you with `quotient.liftOn'` and `quotient.liftOn₂'`.

Example :
```lean
instance : SMul PSL(2, ℝ) ℍ where
  smul g := Quotient.liftOn' g (· • ·) <| by
    intro A B hAB
    rw [@QuotientGroup.leftRel_apply, SpecialLinearGroup.coset_center_iff_2] at hAB
```
-/
theorem coset_center_iff_2
    {A B : SpecialLinearGroup n R} : A⁻¹ * B ∈ Subgroup.center (SpecialLinearGroup n R) ↔
    (B = A ∨ B = -A) := by
  rw [coset_center_iff]
  aesop

end SL2

end SpecialLinearGroup
