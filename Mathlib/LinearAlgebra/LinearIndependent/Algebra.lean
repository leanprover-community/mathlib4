/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence and algebra maps

This file collects results relating linear independence along algebra maps.

These results cannot go in `LinearAlgebra/LinearIndependent/Basic.lean` due to the algebra import.
-/

public section

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [FaithfulSMul S A]

@[simp]
theorem LinearIndependent.algebraMap_comp_iff {ι : Type*} {v : ι → S} :
    LinearIndependent R (algebraMap S A ∘ v) ↔ LinearIndependent R v :=
  (IsScalarTower.toAlgHom R S A).toLinearMap.linearIndependent_iff_of_injOn (by simp)

@[simp]
theorem LinearIndepOn.algebraMap_comp_iff {ι : Type*} {v : ι → S} {s : Set ι} :
    LinearIndepOn R (algebraMap S A ∘ v) s ↔ LinearIndepOn R v s :=
  LinearIndependent.algebraMap_comp_iff

@[simp]
theorem LinearIndepOn.id_image_algebraMap_iff {s : Set S} :
    LinearIndepOn R id (algebraMap S A '' s) ↔ LinearIndepOn R id s :=
  (linearIndepOn_iff_image (by simp)).symm.trans LinearIndepOn.algebraMap_comp_iff
