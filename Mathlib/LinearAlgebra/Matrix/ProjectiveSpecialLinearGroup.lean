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

/-- A projective special linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

namespace SpecialLinearGroup

open SpecialLinearGroup

/-- This is a converter to help you with `quotient.liftOn'` and `quotient.liftOn₂'` for `PSL(n, R)`.

Example :
```lean
instance : SMul PSL(2, ℝ) ℍ where
  smul g := Quotient.liftOn' g (· • ·) <| by
    intro A B hAB
    rw [@QuotientGroup.leftRel_apply] at hAB
    rw [SpecialLinearGroup.coset_center_iff] at hAB
```
-/
theorem coset_center_iff {A B : SpecialLinearGroup n R} :
    A⁻¹ * B ∈ Subgroup.center (SpecialLinearGroup n R) ↔
    ∃ (c : R), (c ^ Fintype.card n = 1 ∧ B.val = c • A.val) := by
  constructor
  · intro hAB
    obtain ⟨c, hAB⟩ := mem_center_iff.mp hAB
    exact ⟨c, hAB.1, by
      rw [@smul_eq_mul_diagonal, ← @scalar_apply, hAB.2, ← @coe_mul, @mul_inv_cancel_left]⟩
  · intro ⟨c, hc, hAB⟩
    exact mem_center_iff.mpr  ⟨c, hc, by simp [hAB, adjugate_mul, smul_one_eq_diagonal]⟩

section SL2

variable [Fact (Even (Fintype.card n))] {hn : Fintype.card n = 2} [NoZeroDivisors R]

/-- This is a converter to help you with `quotient.liftOn'` and `quotient.liftOn₂'` for `PSL(2, R)`.

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
