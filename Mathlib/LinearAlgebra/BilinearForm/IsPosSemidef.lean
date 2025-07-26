/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Positive semidefinite bilinear forms

In this file we define positive bilinear forms as bilinear forms `f : E × E → ℝ` such that for
any `x : E`, `0 ≤ f x x`. We then define positive semidefinite bilinear forms as
symmetric and positive bilinear forms.

## Main definitions

* `LinearMap.BilinForm.IsPos`: A bilinear map `f` is positive if for any `x`, `0 ≤ f x x`.
* `LinearMap.BilinForm.IsPosSemidef`: A bilinear map is positive semidefinite if it is
  symmetric and positive.

## Implementation notes

We only define thes predicate for real bilinear forms as the greater generality should be about
sesquilinear forms.

## TODO

Generalize these definitions to sesquilinear forms.

## Tags

bilinear form, positive, semidefinite
-/

open Module

variable {E n : Type*} [AddCommMonoid E] [Module ℝ E] (f : LinearMap.BilinForm ℝ E)
    (b : Basis n ℝ E)

namespace LinearMap.BilinForm

section IsPos

/-- A bilinear map `f` is positive if for any `x`, `0 ≤ f x x`. -/
structure IsPos : Prop where
  nonneg : ∀ x, 0 ≤ f x x

lemma isPos_def : f.IsPos ↔ ∀ x, 0 ≤ f x x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

end IsPos

section IsPosSemidef

/-- A bilinear map is positive semidefinite if it is symmetric and positive. -/
structure IsPosSemidef : Prop extends f.IsSymm, f.IsPos

variable {f}

lemma IsPosSemidef.isSymm (hf : IsPosSemidef f) :f.IsSymm := hf.toIsSymm

lemma IsPosSemidef.isPos (hf : IsPosSemidef f) : f.IsPos := hf.toIsPos


variable (f) in
lemma isPosSemidef_iff : f.IsPosSemidef ↔ f.IsSymm ∧ f.IsPos where
  mp h := ⟨h.isSymm, h.isPos⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩

variable [Fintype n] [DecidableEq n]

lemma isPosSemidef_iff_posSemidef_toMatrix :
    f.IsPosSemidef ↔ (BilinForm.toMatrix b f).PosSemidef := by
  rw [isPosSemidef_iff, Matrix.PosSemidef, Matrix.isHermitian_iff_isSymm]
  apply and_congr (BilinForm.isSymm_iff_isSymm_toMatrix b f)
  rw [isPos_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [BilinForm.dotProduct_toMatrix_mulVec]
    exact h _
  · rw [BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
    exact h _

end IsPosSemidef

end LinearMap.BilinForm
