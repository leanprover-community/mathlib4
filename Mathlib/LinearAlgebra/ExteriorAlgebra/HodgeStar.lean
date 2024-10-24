/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Finsupp

/-!
Documentation
-/
/-
Hodge star operator or Hodge star is a linear map defined on the exterior algebra of a
finite-dimensional oriented vector space endowed with a nondegenerate symmetric bilinear form.

α = ⋀ α_i , β = ⋀ β_i ∈ ⋀ᵏ V
⟨α , β⟩ = det( ⟨α_i , β_j⟩ )

{e_i} orthonormal basis for V
ω = ⋀ e_i
α ∧ ⋆β = ⟨α , β⟩ ω
-/

noncomputable section InducedBilinearMap

open ExteriorAlgebra Matrix LinearMap

#check det
#check Module.Finite.exists_fin

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (B : LinearMap.BilinForm R M) (Bsymm : B.IsSymm) (Bnondeg : B.Nondegenerate)

def dim : ℕ := (@Module.Finite.exists_fin R M).choose
def s : (Fin (dim R M) → M) := (@Module.Finite.exists_fin R M).choose_spec.choose
def spec : Submodule.span R (Set.range (s R M)) = ⊤ :=
  (@Module.Finite.exists_fin R M).choose_spec.choose_spec

theorem span : ∀ (m : M), ∃ (c : Fin (dim R M) → R),
  ∑ i : Fin (dim R M), c i • (s R M) i = m := by
  intro m
  rw [← mem_span_range_iff_exists_fun R, spec]
  exact Submodule.mem_top

#check span

def F (ι₁ : Fin (dim R M) → R) (ι₂ : Fin (dim R M) → R) : R :=
  det (of fun (i : Fin (dim R M)) (j : Fin (dim R M)) ↦ (ι₁ i) * (ι₂ j) * B (s R M i) (s R M j) )

def F2 : M → M → R := fun m n ↦ F R M B (span R M m).choose (span R M n).choose



def B2 (k : ℕ) : LinearMap.BilinForm R (⋀[R]^k M) where
  toFun := sorry
  map_add' := sorry
  map_smul' := sorry


end InducedBilinearMap
