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

# Base change of exterior power

In this file, we proved that exterior power commutes with arbitrary base change.

# Main Results

* `exteriorPower.baseChangeEquiv`: for `R`-algebra `S`, the base change isomorphism
  `S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M)`

-/

noncomputable section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

namespace exteriorPower

/-- The alternating map obtained from `ExteriorAlgebra.ιMulti` on compositing with
`TensorProduct.mk R S M 1`. -/
def baseChangeGenerator (i : ℕ) : M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m := ExteriorAlgebra.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' _ := by simp [Function.comp_update, map_add]
  map_update_smul' {_} m j r := by
    simp [Function.comp_update, -algebraMap_smul, ← algebraMap_smul S r]
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : ((mk R S M 1) ∘ m) j = ((mk R S M 1) ∘ m) k := by
      simpa using congrArg (TensorProduct.mk R S M 1) hjk
    simpa using
      (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq (((TensorProduct.mk R S M 1) ∘ m)) this hjk_ne

/-- Auxiliary alternating map for `exteriorPower.baseChangeEquivForward`. -/
def baseChangeEquivForwardAux (i : ℕ) : M [⋀^Fin i]→ₗ[R] (⋀[S]^i (S ⊗[R] M)) :=
  (baseChangeGenerator R M S i).codRestrict ((⋀[S]^i (S ⊗[R] M)).restrictScalars R) (fun m =>
    ExteriorAlgebra.ιMulti_range S i (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m)))

/-- Forward function of `exteriorPower.baseChangeEquiv`, lift from the map
`(⋀[R]^i M) →ₗ[R] ⋀[S]^i (S ⊗[R] M)` corresponding to `exteriorPower.baseChangeEquivForwardAux`. -/
def baseChangeEquivForward (i : ℕ) : S ⊗[R] (⋀[R]^i M) →ₗ[S] (⋀[S]^i (S ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun s := s • exteriorPower.alternatingMapLinearEquiv (baseChangeEquivForwardAux R M S i)
    map_add' s t := by simp [add_smul]
    map_smul' s t := by simp [smul_smul] }

lemma baseChangeEquivForward_apply_one_tmul_ιMulti (i : ℕ) (m : Fin i → M) :
    baseChangeEquivForward R M S i (1 ⊗ₜ[R] ιMulti R i m) =
      ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  rw [exteriorPower.baseChangeEquivForward, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Auxiliary alternating map for `exteriorPower.baseChangeEquivInverse`. -/
def baseChangeInverseAlternating (i : ℕ) : (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  (((ExteriorAlgebra.toExteriorPower R M i).baseChange S).comp
    (ExteriorAlgebra.baseChangeEquiv R M S).symm.toAlgHom.toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti S i)

lemma baseChangeInverseAlternating_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeInverseAlternating R M S i (fun j ↦ s j ⊗ₜ[R] m j) =
      (∏ j, s j) ⊗ₜ[R] exteriorPower.ιMulti R i m := by
  trans ((ExteriorAlgebra.toExteriorPower R M i).baseChange S)
    ((∏ j, s j) ⊗ₜ[R] (ExteriorAlgebra.ιMulti R i) m)
  · simp only [baseChangeInverseAlternating, AlgEquiv.toAlgHom_toLinearMap, LinearMap.coe_comp,
      AlgEquiv.toLinearEquiv_symm, LinearMap.compAlternatingMap_apply, Function.comp_apply,
      LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv, ExteriorAlgebra.ιMulti_apply]
    congr
    induction i with
    | zero => simp [Algebra.TensorProduct.one_def]
    | succ i ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, map_mul, ih,
        ExteriorAlgebra.baseChangeEquiv_symm_apply, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [Fin.prod_univ_succAbove s 0, Fin.zero_succAbove]
  · simp [← exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.toExteriorPower_eq]

/-- Inverse function of `exteriorPower.baseChangeEquiv`,
obtained from `exteriorPower.baseChangeInverseAlternating`. -/
def baseChangeEquivInverse (i : ℕ) : ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  alternatingMapLinearEquiv (baseChangeInverseAlternating R M S i)

lemma baseChangeEquivInverse_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeEquivInverse R M S i (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [baseChangeEquivInverse, baseChangeInverseAlternating_apply_tmul]

lemma baseChange_left_inverse (i : ℕ) :
    (baseChangeEquivInverse R M S i).comp (baseChangeEquivForward R M S i) = LinearMap.id := by
  ext m
  have : (TensorProduct.mk R S M 1) ∘ m = fun j ↦ 1 ⊗ₜ[R] m j := rfl
  simp [baseChangeEquivForward_apply_one_tmul_ιMulti, baseChangeEquivInverse, this,
    baseChangeInverseAlternating_apply_tmul R M S i (fun _ ↦ 1) m]

lemma baseChangeEquivForward_surjective (i : ℕ) :
    Function.Surjective (baseChangeEquivForward R M S i) := by
  have eqtop : Submodule.span S (Set.range (TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M)) = ⊤ := by
    rw [← Set.image_univ, ← Submodule.baseChange_span, Submodule.span_univ,
      Submodule.baseChange_top]
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ιMulti_span_of_span S i _ eqtop,
    Submodule.span_le, Set.image_subset_iff]
  intro a ha
  let m (j : Fin i) : M := Classical.choose (ha (Set.mem_range_self j))
  have aeq : a = (TensorProduct.mk R S M 1) ∘ m := by
    ext j
    exact (Classical.choose_spec (ha (Set.mem_range_self j))).symm
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_range, aeq]
  use 1 ⊗ₜ[R] ιMulti R i m
  rw [baseChangeEquivForward_apply_one_tmul_ιMulti]

lemma baseChange_right_inverse (i : ℕ) :
    (baseChangeEquivForward R M S i).comp (baseChangeEquivInverse R M S i) = LinearMap.id := by
  refine LinearMap.ext (fun x ↦ ?_)
  rcases baseChangeEquivForward_surjective R M S i x with ⟨y, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [← LinearMap.comp_apply _ _ y, exteriorPower.baseChange_left_inverse, LinearMap.id_coe, id_eq]

/-- The commute of exterior power and base change. -/
public def baseChangeEquiv (i : ℕ) : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) where
  __ := baseChangeEquivForward R M S i
  invFun := baseChangeEquivInverse R M S i
  left_inv x := congr($(exteriorPower.baseChange_left_inverse R M S i) x)
  right_inv x := congr($(exteriorPower.baseChange_right_inverse R M S i) x)

public lemma baseChangeEquiv_apply_tmul (i : ℕ) (m : Fin i → M) :
    baseChangeEquiv R M S i (1 ⊗ₜ[R] (ιMulti R i m)) =
      ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  simp [exteriorPower.baseChangeEquiv, baseChangeEquivForward_apply_one_tmul_ιMulti]

public lemma baseChangeEquiv_symm_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    (baseChangeEquiv R M S i).symm (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [exteriorPower.baseChangeEquiv, exteriorPower.baseChangeEquivInverse_apply_tmul]

end exteriorPower
