/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Tensor product of projections -/

@[expose] public section

open Submodule TensorProduct LinearMap

variable (R : Type*) [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module A M] {M₁ M₂ : Submodule A M}

namespace LinearMap

variable (hM : IsCompl M₁ M₂) (Q : Type*) [AddCommGroup Q] [Module A Q]

theorem ker_lTensor_projectionOnto :
    ker (lTensor Q (projectionOnto _ _ hM)) = range (lTensor Q M₂.subtype) := by
  rw [← exact_iff]
  apply lTensor_exact
  · simp only [exact_iff, range_subtype, ker_projectionOnto]
  · simp [← LinearMap.range_eq_top]

theorem ker_rTensor_projectionOnto :
    ker (rTensor Q (projectionOnto _ _ hM)) = range (rTensor Q M₂.subtype) := by
  rw [← exact_iff]
  apply rTensor_exact
  · simp only [exact_iff, range_subtype, ker_projectionOnto]
  · simp [← LinearMap.range_eq_top]

theorem ker_baseChange_projectionOnto (R : Type*) [CommRing R] [Algebra A R] :
    ker (baseChange R (projectionOnto _ _ hM)) =
      range (baseChange R M₂.subtype) := by
  simpa [← exact_iff] using ker_lTensor_projectionOnto hM R

theorem isCompl_lTensor (hM : IsCompl M₁ M₂) :
    IsCompl (range (lTensor Q M₁.subtype)) (range (lTensor Q M₂.subtype)) := by
  have hq :
    M₁.subtype.comp (projectionOnto _ _ hM)
      + M₂.subtype.comp (projectionOnto _ _ hM.symm) = LinearMap.id := by
    ext x
    simp only [add_apply, LinearMap.coe_comp, coe_subtype, Function.comp_apply, id_coe, id_eq]
    erw [projection_add_projection_eq_self]
  apply IsCompl.mk
  · rw [disjoint_def]
    intro x h h'
    rw [← id_apply x (R := A), ← lTensor_id, ← hq]
    simp only [lTensor_add, lTensor_comp,
      LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← ker_lTensor_projectionOnto hM Q] at h'
    rw [← ker_lTensor_projectionOnto hM.symm Q] at h
    rw [LinearMap.mem_ker] at h h'
    simp only [h', _root_.map_zero, h, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [← lTensor_id_apply Q _ x, ← hq]
    simp only [lTensor_add, lTensor_comp, add_apply, LinearMap.coe_comp, Function.comp_apply]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))

theorem isCompl_rTensor (Q : Type*) [AddCommGroup Q] [Module A Q] (hM : IsCompl M₁ M₂) :
    IsCompl (range (rTensor Q M₁.subtype)) (range (rTensor Q M₂.subtype)) := by
  simp only [← comm_comp_lTensor_comp_comm_eq, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]
  exact isCompl_map (TensorProduct.comm A Q M) (isCompl_lTensor Q hM)

theorem isCompl_baseChange (hM : IsCompl M₁ M₂) (R : Type*) [CommRing R] [Algebra A R] :
    IsCompl (range (baseChange R M₁.subtype)) (range (baseChange R M₂.subtype)) := by
  rw [← isCompl_restrictScalars_iff A]
  exact isCompl_lTensor R hM

end LinearMap
