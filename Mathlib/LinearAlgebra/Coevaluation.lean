/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.Contraction

#align_import linear_algebra.coevaluation from "leanprover-community/mathlib"@"d6814c584384ddf2825ff038e868451a7c956f31"

/-!
# The coevaluation map on finite dimensional vector spaces

Given a finite dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ Dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/


noncomputable section

section coevaluation

open TensorProduct FiniteDimensional

open TensorProduct BigOperators

universe u v

variable (K : Type u) [Field K]

variable (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite dimensional
  vector space `V`. -/
def coevaluation : K →ₗ[K] V ⊗[K] Module.Dual K V :=
  let bV := Basis.ofVectorSpace K V
  (Basis.singleton Unit K).constr K fun _ =>
    ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i
#align coevaluation coevaluation

theorem coevaluation_apply_one :
    (coevaluation K V) (1 : K) =
      let bV := Basis.ofVectorSpace K V
      ∑ i : Basis.ofVectorSpaceIndex K V, bV i ⊗ₜ[K] bV.coord i := by
  simp only [coevaluation, id]
  -- ⊢ ↑(↑(Basis.constr (Basis.singleton Unit K) K) fun x => ∑ x : ↑(Basis.ofVector …
  rw [(Basis.singleton Unit K).constr_apply_fintype K]
  -- ⊢ ∑ i : Unit, ↑(Basis.equivFun (Basis.singleton Unit K)) 1 i • ∑ x : ↑(Basis.o …
  simp only [Fintype.univ_punit, Finset.sum_const, one_smul, Basis.singleton_repr,
    Basis.equivFun_apply, Basis.coe_ofVectorSpace, one_nsmul, Finset.card_singleton]
#align coevaluation_apply_one coevaluation_apply_one

open TensorProduct

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
theorem contractLeft_assoc_coevaluation :
    (contractLeft K V).rTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).symm.toLinearMap ∘ₗ
          (coevaluation K V).lTensor (Module.Dual K V) =
      (TensorProduct.lid K _).symm.toLinearMap ∘ₗ (TensorProduct.rid K _).toLinearMap := by
  letI := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  -- ⊢ LinearMap.comp (LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (Lin …
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (mk K (Module.Dual K V) K) (LinearMap.comp (LinearMap.rTens …
  apply (Basis.ofVectorSpace K V).dualBasis.ext; intro j; apply LinearMap.ext_ring
  -- ⊢ ∀ (i : ↑(Basis.ofVectorSpaceIndex K V)), ↑(LinearMap.compr₂ (mk K (Module.Du …
                                                 -- ⊢ ↑(LinearMap.compr₂ (mk K (Module.Dual K V) K) (LinearMap.comp (LinearMap.rTe …
                                                          -- ⊢ ↑(↑(LinearMap.compr₂ (mk K (Module.Dual K V) K) (LinearMap.comp (LinearMap.r …
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
  -- ⊢ ↑(LinearMap.comp (LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (L …
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  -- ⊢ ↑(LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (↑(LinearEquiv.sym …
  rw [rid_tmul, one_smul, lid_symm_apply]
  -- ⊢ ↑(LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (↑(LinearEquiv.sym …
  simp only [LinearEquiv.coe_toLinearMap, LinearMap.lTensor_tmul, coevaluation_apply_one]
  -- ⊢ ↑(LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (↑(LinearEquiv.sym …
  rw [TensorProduct.tmul_sum, LinearEquiv.map_sum]; simp only [assoc_symm_tmul]
  -- ⊢ ↑(LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (∑ i : ↑(Basis.ofV …
                                                    -- ⊢ ↑(LinearMap.rTensor (Module.Dual K V) (contractLeft K V)) (∑ x : ↑(Basis.ofV …
  rw [LinearMap.map_sum]; simp only [LinearMap.rTensor_tmul, contractLeft_apply]
  -- ⊢ ∑ i : ↑(Basis.ofVectorSpaceIndex K V), ↑(LinearMap.rTensor (Module.Dual K V) …
                          -- ⊢ ∑ x : ↑(Basis.ofVectorSpaceIndex K V), ↑(↑(Basis.dualBasis (Basis.ofVectorSp …
  simp only [Basis.coe_dualBasis, Basis.coord_apply, Basis.repr_self_apply, TensorProduct.ite_tmul]
  -- ⊢ (∑ x : ↑(Basis.ofVectorSpaceIndex K V), if x = j then 1 ⊗ₜ[K] Basis.coord (B …
  rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]
  -- ⊢ (if j ∈ Finset.univ then 1 ⊗ₜ[K] Basis.coord (Basis.ofVectorSpace K V) j els …
                           -- 🎉 no goals
#align contract_left_assoc_coevaluation contractLeft_assoc_coevaluation

/-- This lemma corresponds to one of the coherence laws for duals in rigid categories, see
  `CategoryTheory.Monoidal.Rigid`. -/
theorem contractLeft_assoc_coevaluation' :
    (contractLeft K V).lTensor _ ∘ₗ
        (TensorProduct.assoc K _ _ _).toLinearMap ∘ₗ (coevaluation K V).rTensor V =
      (TensorProduct.rid K _).symm.toLinearMap ∘ₗ (TensorProduct.lid K _).toLinearMap := by
  letI := Classical.decEq (Basis.ofVectorSpaceIndex K V)
  -- ⊢ LinearMap.comp (LinearMap.lTensor V (contractLeft K V)) (LinearMap.comp (↑(T …
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (mk K K V) (LinearMap.comp (LinearMap.lTensor V (contractLe …
  apply LinearMap.ext_ring; apply (Basis.ofVectorSpace K V).ext; intro j
  -- ⊢ ↑(LinearMap.compr₂ (mk K K V) (LinearMap.comp (LinearMap.lTensor V (contract …
                            -- ⊢ ∀ (i : ↑(Basis.ofVectorSpaceIndex K V)), ↑(↑(LinearMap.compr₂ (mk K K V) (Li …
                                                                 -- ⊢ ↑(↑(LinearMap.compr₂ (mk K K V) (LinearMap.comp (LinearMap.lTensor V (contra …
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
  -- ⊢ ↑(LinearMap.comp (LinearMap.lTensor V (contractLeft K V)) (LinearMap.comp (↑ …
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  -- ⊢ ↑(LinearMap.lTensor V (contractLeft K V)) (↑(TensorProduct.assoc K V (Module …
  rw [lid_tmul, one_smul, rid_symm_apply]
  -- ⊢ ↑(LinearMap.lTensor V (contractLeft K V)) (↑(TensorProduct.assoc K V (Module …
  simp only [LinearEquiv.coe_toLinearMap, LinearMap.rTensor_tmul, coevaluation_apply_one]
  -- ⊢ ↑(LinearMap.lTensor V (contractLeft K V)) (↑(TensorProduct.assoc K V (Module …
  rw [TensorProduct.sum_tmul, LinearEquiv.map_sum]; simp only [assoc_tmul]
  -- ⊢ ↑(LinearMap.lTensor V (contractLeft K V)) (∑ i : ↑(Basis.ofVectorSpaceIndex  …
                                                    -- ⊢ ↑(LinearMap.lTensor V (contractLeft K V)) (∑ x : ↑(Basis.ofVectorSpaceIndex  …
  rw [LinearMap.map_sum]; simp only [LinearMap.lTensor_tmul, contractLeft_apply]
  -- ⊢ ∑ i : ↑(Basis.ofVectorSpaceIndex K V), ↑(LinearMap.lTensor V (contractLeft K …
                          -- ⊢ ∑ x : ↑(Basis.ofVectorSpaceIndex K V), ↑(Basis.ofVectorSpace K V) x ⊗ₜ[K] ↑( …
  simp only [Basis.coord_apply, Basis.repr_self_apply, TensorProduct.tmul_ite]
  -- ⊢ (∑ x : ↑(Basis.ofVectorSpaceIndex K V), if j = x then ↑(Basis.ofVectorSpace  …
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]
  -- ⊢ (if j ∈ Finset.univ then ↑(Basis.ofVectorSpace K V) j ⊗ₜ[K] 1 else 0) = ↑(Ba …
                          -- 🎉 no goals
#align contract_left_assoc_coevaluation' contractLeft_assoc_coevaluation'

end coevaluation
