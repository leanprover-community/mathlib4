/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Positive semidefinite sesquilinear forms

In this file we define positive sesquilinear forms as sesquilinear forms `f : E × E → R` such that
for any `x : E`, `0 ≤ f x x`. We then define positive semidefinite sesquilinear forms as
symmetric and positive sesquilinear forms.

## Main definitions

* `SesquilinForm.IsPos`: A sesquilinear map `f` is positive if for any `x`, `0 ≤ f x x`.
* `SesquilinForm.IsPosSemidef`: A sesquilinear map is positive semidefinite if it is
  symmetric and positive.

## Tags

sesquilinear form, positive, semidefinite
-/

open Module (Basis)

variable {E n R : Type*} [AddCommMonoid E] [CommRing R] [StarRing R] [Module R E]
    {f : SesquilinForm R E} (b : Basis n R E)

namespace SesquilinForm

section IsPos

variable [LE R]

variable (f) in
/-- A sesquilinear map `f` is positive if for any `x`, `0 ≤ f x x`. -/
structure IsPos : Prop where
  nonneg : ∀ x, 0 ≤ f x x

lemma isPos_def : f.IsPos ↔ ∀ x, 0 ≤ f x x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

end IsPos

section IsPosSemidef

section Def

variable [LE R]

variable (f) in
/-- A sesquilinear map is positive semidefinite if it is symmetric and positive. -/
structure IsPosSemidef : Prop extends f.IsSymm, f.IsPos

lemma IsPosSemidef.isSymm (hf : IsPosSemidef f) : f.IsSymm := hf.toIsSymm

lemma IsPosSemidef.isPos (hf : IsPosSemidef f) : f.IsPos := hf.toIsPos

lemma isPosSemidef_iff : f.IsPosSemidef ↔ f.IsSymm ∧ f.IsPos where
  mp h := ⟨h.isSymm, h.isPos⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩

end Def

lemma isPosSemidef_iff_posSemidef_toMatrix [Fintype n] [PartialOrder R] :
    f.IsPosSemidef ↔ (f.toMatrix b).PosSemidef := by
  rw [isPosSemidef_iff, Matrix.PosSemidef, SesquilinForm.isSymm_iff_isHermitian_toMatrix b,
    isPos_def]
  refine and_congr .rfl ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [dotProduct_toMatrix_mulVec]
    exact h _
  · rw [← apply_eq_dotProduct_toMatrix_mulVec b]
    exact h _

end IsPosSemidef

end SesquilinForm
