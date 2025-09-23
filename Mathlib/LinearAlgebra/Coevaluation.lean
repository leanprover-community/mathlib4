/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.Contraction

/-!
# The coevaluation map on finite-dimensional vector spaces

Given a finite-dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ Dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/


noncomputable section

section coevaluation

open TensorProduct Module

open TensorProduct

universe u v

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite-dimensional
  vector space `V`. -/
def coevaluation : K →ₗ[K] V ⊗[K] Module.Dual K V :=
  let bV := Basis.ofVectorSpace K V
  (Basis.singleton Unit K).constr K fun _ =>
    ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i

theorem coevaluation_apply_one :
    (coevaluation K V) (1 : K) =
      let bV := Basis.ofVectorSpace K V
      ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i := by
  simp only [coevaluation]
  rw [(Basis.singleton Unit K).constr_apply_fintype K]
  simp only [Fintype.univ_punit, Finset.sum_const, one_smul, Basis.singleton_repr,
    Basis.equivFun_apply, Basis.coe_ofVectorSpace, Finset.card_singleton]

open TensorProduct

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
theorem contractLeft_assoc_coevaluation :
    (contractLeft K V).rTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).symm.toLinearMap ∘ₗ
          (coevaluation K V).lTensor (Module.Dual K V) =
      (TensorProduct.lid K _).symm.toLinearMap ∘ₗ (TensorProduct.rid K _).toLinearMap := by
  letI := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  apply TensorProduct.ext
  apply (Basis.ofVectorSpace K V).dualBasis.ext; intro j; apply LinearMap.ext_ring
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [rid_tmul, one_smul, lid_symm_apply]
  simp only [LinearMap.lTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.tmul_sum, map_sum]; simp only [assoc_symm_tmul]
  rw [map_sum]; simp only [LinearMap.rTensor_tmul, contractLeft_apply]
  simp only [Basis.coe_dualBasis, Basis.coord_apply, Basis.repr_self_apply, TensorProduct.ite_tmul]
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
theorem contractLeft_assoc_coevaluation' :
    (contractLeft K V).lTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).toLinearMap ∘ₗ (coevaluation K V).rTensor V =
      (TensorProduct.rid K _).symm.toLinearMap ∘ₗ (TensorProduct.lid K _).toLinearMap := by
  letI := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  apply TensorProduct.ext
  apply LinearMap.ext_ring; apply (Basis.ofVectorSpace K V).ext; intro j
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [lid_tmul, one_smul, rid_symm_apply]
  simp only [LinearMap.rTensor_tmul, coevaluation_apply_one]
  rw [TensorProduct.sum_tmul, map_sum]; simp only [assoc_tmul]
  rw [map_sum]; simp only [LinearMap.lTensor_tmul, contractLeft_apply]
  simp only [Basis.coord_apply, Basis.repr_self_apply, TensorProduct.tmul_ite]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]

end coevaluation
