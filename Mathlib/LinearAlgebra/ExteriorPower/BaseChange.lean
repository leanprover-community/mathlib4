/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Base change of exterior powers

This file contains a proof that exterior powers commute with base change.

## Main results

* `exteriorPower.baseChangeEquiv`: for an `R`-algebra `S`, the base change isomorphism
  `S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M)`.
-/

noncomputable section

variable (R M S : Type*) [CommRing R] [AddCommGroup M] [Module R M] [CommRing S] [Algebra R S]
  (i : ℕ)

open Function Set TensorProduct

namespace exteriorPower

section Auxiliary

/-- The alternating map `(m₁, m₂, …, mᵢ) ↦ (1 ⊗ m₁) ∧ (1 ⊗ m₂) ∧ ⋯ ∧ (1 ⊗ mᵢ)`.

This is an auxiliary definition used only to construct `baseChangeEquivForwardAux` below. -/
def baseChangeGenerator : M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m := ExteriorAlgebra.ιMulti S i (mk R S M 1 ∘ m)
  map_update_add' _ := by simp [comp_update, map_add]
  map_update_smul' {_} m j r := by
    simp [comp_update, -algebraMap_smul, ← algebraMap_smul S r]
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : (mk R S M 1 ∘ m) j = (mk R S M 1 ∘ m) k := by simpa using congrArg (mk R S M 1) hjk
    simpa using (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq (mk R S M 1 ∘ m) this hjk_ne

/-- Auxiliary alternating map for `exteriorPower.baseChangeEquivForward`. -/
def baseChangeEquivForwardAux : M [⋀^Fin i]→ₗ[R] ⋀[S]^i (S ⊗[R] M) :=
  (baseChangeGenerator R M S i).codRestrict ((⋀[S]^i (S ⊗[R] M)).restrictScalars R)
    (fun m ↦ ExteriorAlgebra.ιMulti_range S i (mem_range_self (mk R S M 1 ∘ m)))

/-- Forward map of `exteriorPower.baseChangeEquiv`: the base change of the linear map
`⋀[R]^i M →ₗ[R] ⋀[S]^i (S ⊗[R] M)` corresponding to `exteriorPower.baseChangeEquivForwardAux`. -/
def baseChangeEquivForward : S ⊗[R] (⋀[R]^i M) →ₗ[S] ⋀[S]^i (S ⊗[R] M) :=
  (alternatingMapLinearEquiv (baseChangeEquivForwardAux R M S i)).liftBaseChange S

lemma baseChangeEquivForward_tmul_ιMulti (s : S) (m : Fin i → M) :
    baseChangeEquivForward R M S i (s ⊗ₜ[R] ιMulti R i m) =
      s • ιMulti S i (fun j ↦ 1 ⊗ₜ m j) := by
  simp [baseChangeEquivForward]
  rfl

/-- Auxiliary alternating map for `exteriorPower.baseChangeEquivInverse`. -/
def baseChangeInverseAlternating : (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  (((ExteriorAlgebra.toExteriorPower R M i).baseChange S).comp
    (ExteriorAlgebra.baseChangeEquiv R M S).symm.toAlgHom.toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti S i)

lemma baseChangeInverseAlternating_apply_tmul (s : Fin i → S) (m : Fin i → M) :
    baseChangeInverseAlternating R M S i (fun j ↦ s j ⊗ₜ[R] m j) =
      (∏ j, s j) ⊗ₜ[R] ιMulti R i m := by
  simp only [baseChangeInverseAlternating, LinearMap.compAlternatingMap_apply,
    LinearMap.comp_apply, AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearMap_apply,
    ExteriorAlgebra.baseChangeEquiv_symm_ιMulti_tmul, LinearMap.baseChange_tmul]
  rw [← ιMulti_apply_coe, ExteriorAlgebra.toExteriorPower_coe]

/-- Inverse map of `exteriorPower.baseChangeEquiv`,
obtained from `exteriorPower.baseChangeInverseAlternating`. -/
def baseChangeEquivInverse : ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  alternatingMapLinearEquiv (baseChangeInverseAlternating R M S i)

lemma baseChangeEquivInverse_ιMulti_tmul (s : Fin i → S) (m : Fin i → M) :
    baseChangeEquivInverse R M S i (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (∏ j, s j) ⊗ₜ[R] ιMulti R i m := by
  simp [baseChangeEquivInverse, baseChangeInverseAlternating_apply_tmul]

lemma baseChangeEquivInverse_comp_baseChangeEquivForward :
    (baseChangeEquivInverse R M S i).comp (baseChangeEquivForward R M S i) = LinearMap.id := by
  ext m
  simp [baseChangeEquivForward_tmul_ιMulti,
    baseChangeEquivInverse_ιMulti_tmul R M S i (fun _ ↦ 1) m]

lemma leftInverse_baseChangeEquivInverse :
    LeftInverse (baseChangeEquivInverse R M S i) (baseChangeEquivForward R M S i) :=
  LinearMap.congr_fun (baseChangeEquivInverse_comp_baseChangeEquivForward R M S i)

lemma baseChangeEquivForward_surjective :
    Surjective (baseChangeEquivForward R M S i) := by
  have eqtop : Submodule.span S (range (mk R S M 1 : M →ₗ[R] S ⊗[R] M)) = ⊤ := by
    rw [← image_univ, ← Submodule.baseChange_span, Submodule.span_univ, Submodule.baseChange_top]
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ιMulti_span_of_span S i _ eqtop, Submodule.span_le,
    image_subset_iff]
  intro a ha
  obtain ⟨m, rfl⟩ := range_subset_range_iff_exists_comp.mp ha
  exact ⟨1 ⊗ₜ ιMulti R i m, by simp [baseChangeEquivForward_tmul_ιMulti, comp_def]⟩

end Auxiliary

/-- Exterior powers commute with base change. -/
public def baseChangeEquiv : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) where
  __ := baseChangeEquivForward R M S i
  invFun := baseChangeEquivInverse R M S i
  left_inv := leftInverse_baseChangeEquivInverse R M S i
  right_inv := (leftInverse_baseChangeEquivInverse R M S i).rightInverse_of_surjective
    (baseChangeEquivForward_surjective R M S i)

variable {R M S i}

@[simp]
public lemma baseChangeEquiv_tmul_ιMulti (s : S) (m : Fin i → M) :
    baseChangeEquiv R M S i (s ⊗ₜ[R] ιMulti R i m) = s • ιMulti S i (fun j ↦ 1 ⊗ₜ m j) :=
  baseChangeEquivForward_tmul_ιMulti R M S i s m

@[simp]
public lemma baseChangeEquiv_symm_ιMulti_tmul (s : Fin i → S) (m : Fin i → M) :
    (baseChangeEquiv R M S i).symm (ιMulti S i fun j ↦ s j ⊗ₜ[R] m j) =
      (∏ j, s j) ⊗ₜ[R] ιMulti R i m :=
  baseChangeEquivInverse_ιMulti_tmul R M S i s m

end exteriorPower
