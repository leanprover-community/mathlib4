/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!

# Base change of exterior power

-/

public section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

namespace ExteriorAlgebra

/-- Helper for KoszulComplex baseChangeIso: the tensor-side generator map
`s ⊗ m ↦ s ⊗ ι_R(m)` into the base-changed exterior algebra. -/
noncomputable def baseChangeι : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M).baseChange S

/-- Helper for KoszulComplex baseChangeIso: tensor generators anticommute in the
base-changed exterior algebra. -/
lemma baseChangeι_mul_add_swap (x y : S ⊗[R] M) :
    ExteriorAlgebra.baseChangeι R M S x * ExteriorAlgebra.baseChangeι R M S y +
      ExteriorAlgebra.baseChangeι R M S y * ExteriorAlgebra.baseChangeι R M S x = 0 := by
  -- Reduce the anticommutation relation to pure tensors in each variable.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [ExteriorAlgebra.baseChangeι]
  · intro s m
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp [ExteriorAlgebra.baseChangeι]
    · intro t n
      simp [ExteriorAlgebra.baseChangeι, Algebra.TensorProduct.tmul_mul_tmul,
        ExteriorAlgebra.ι_add_mul_swap, mul_comm, ← TensorProduct.tmul_add]
    · intro y₁ y₂ hy₁ hy₂
      simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg₂ HAdd.hAdd hy₁ hy₂
  · intro x₁ x₂ hx₁ hx₂
    simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
      congrArg₂ HAdd.hAdd hx₁ hx₂

/-- Helper for KoszulComplex baseChangeIso: every tensor generator squares to zero in
the base-changed exterior algebra. -/
lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  -- Check the square-zero relation by induction on the tensor and use the anticommutation lemma
  -- for the cross term in the add case.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [ExteriorAlgebra.baseChangeι]
  · intro s m
    simp [ExteriorAlgebra.baseChangeι, Algebra.TensorProduct.tmul_mul_tmul]
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, add_left_comm, add_assoc]
    simp [hx, hy, ExteriorAlgebra.baseChangeι_mul_add_swap R M S x y]

/-- Helper for KoszulComplex baseChangeIso: the ambient exterior-algebra map from
`ExteriorAlgebra S (S ⊗[R] M)` to `S ⊗[R] ExteriorAlgebra R M`. -/
noncomputable def baseChangeExteriorAlgebraToTensor :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨ExteriorAlgebra.baseChangeι R M S, ExteriorAlgebra.baseChangeι_sq_zero R M S⟩

end ExteriorAlgebra

namespace exteriorPower

instance : IsScalarTower R S (ExteriorAlgebra S (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

lemma baseChangeGenerator_map_update_add (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (x y : M) :
    (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j (x + y)) =
      (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j x) +
        (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j y) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (x + y), hz x, hz y, map_add, (ExteriorAlgebra.ιMulti S i).map_update_add]

lemma baseChangeGenerator_map_update_smul (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (r : R) (x : M) :
    (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j (r • x)) =
      r • (ExteriorAlgebra.ιMulti S i) (((mk R S M) 1) ∘ Function.update m j x) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (r • x), hz x]
  simpa using (ExteriorAlgebra.ιMulti S i).map_update_smul
    (((TensorProduct.mk R S M 1) ∘ m)) j (algebraMap R S r) ((TensorProduct.mk R S M 1) x)

noncomputable def baseChangeGenerator (i : ℕ) :
    M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m := ExteriorAlgebra.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' := baseChangeGenerator_map_update_add R M S i
  map_update_smul' := baseChangeGenerator_map_update_smul R M S i
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : (((mk R S M) 1) ∘ m) j = (((mk R S M) 1) ∘ m) k := by
      simpa [Function.comp] using congrArg ((TensorProduct.mk R S M 1)) hjk
    -- Equal coordinates after applying `1 ⊗ -` force the alternating expression to vanish.
    simpa [Function.comp] using (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq
      (((TensorProduct.mk R S M 1) ∘ m)) this hjk_ne

/-- Helper for KoszulComplex baseChangeIso: the generator-side alternating map
`m ↦ ιMulti_S (1 ⊗ m)` cod-restricted to the fixed-degree summand. -/
noncomputable def baseChangeIsoForwardAux (i : ℕ) :
    M [⋀^Fin i]→ₗ[R] (⋀[S]^i (S ⊗[R] M)) :=
  (baseChangeGenerator R M S i).codRestrict (((⋀[S]^i (S ⊗[R] M)).restrictScalars R)) (fun m =>
    ExteriorAlgebra.ιMulti_range S i (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m)))

/-- Helper for KoszulComplex baseChangeIso: the forward linear map before upgrading
from the restricted-scalars target to the `S`-linear equivalence. -/
noncomputable def baseChangeIsoForward (i : ℕ) :
    S ⊗[R] (⋀[R]^i M) →ₗ[S] (⋀[S]^i (S ⊗[R] M)) :=
  -- Tensor-lift the `R`-linear map so the scalar on the left tensor factor acts on the target.
  TensorProduct.AlgebraTensorModule.lift {
    toFun s := s • exteriorPower.alternatingMapLinearEquiv (baseChangeIsoForwardAux R M S i)
    map_add' s t := by simp [add_smul]
    map_smul' s t := by simp [smul_smul] }

/-- Helper for KoszulComplex baseChangeIso: the forward map sends the pure generator
`1 ⊗ ιMulti_R m` to `ιMulti_S (1 ⊗ m)`. -/
lemma baseChangeIsoForward_apply_one_tmul_ιMulti (i : ℕ) (m : Fin i → M) :
    baseChangeIsoForward R M S i (1 ⊗ₜ[R] ιMulti R i m) =
      ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  rw [exteriorPower.baseChangeIsoForward, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Helper for KoszulComplex baseChangeIso: the degree-`i` projection out of the exterior algebra,
implemented by the `liftAlternating` family that is zero away from degree `i`. -/
noncomputable def degreeProjection (i : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
  ExteriorAlgebra.liftAlternating (R := R) (M := M) (N := (⋀[R]^i M))
    (Function.update 0 i (exteriorPower.ιMulti R i))

/-- Helper for KoszulComplex baseChangeIso: the degree projection is the identity on
the canonical degree-`i` generator. -/
lemma degreeProjection_apply_ιMulti (i : ℕ) (m : Fin i → M) :
    degreeProjection R M i (ExteriorAlgebra.ιMulti R i m) = ιMulti R i m := by
  -- `liftAlternating` returns the updated family on the matching degree.
  rw [exteriorPower.degreeProjection]
  simp

/-- Helper for KoszulComplex baseChangeIso: the inverse-side alternating map obtained by
passing through the ambient exterior algebra and then projecting to degree `i`. -/
noncomputable def baseChangeInverseAlternating (i : ℕ) :
    (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  (((exteriorPower.degreeProjection R M i).baseChange S).comp
    (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S).toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti S i)

/-- Helper for KoszulComplex baseChangeIso: the inverse-side alternating map sends a tuple of
pure tensors to the scalar product tensor the degree-`i` exterior generator. -/
lemma baseChangeInverseAlternating_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeInverseAlternating R M S i (fun j ↦ s j ⊗ₜ[R] m j) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] exteriorPower.ιMulti R i m := by
  -- Expand the ambient `ιMulti`, evaluate the lift on generators, and then project to degree `i`.
  simp only [baseChangeInverseAlternating, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.ιMulti_apply]
  have hprod : (List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j)).prod =
    (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] (List.ofFn fun j ↦ ExteriorAlgebra.ι R (m j)).prod := by
    induction i with
    | zero => simp [Algebra.TensorProduct.one_def]
    | succ i ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Fin.prod_univ_succ]
  rw [map_list_prod (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S)]
  have himages : List.map (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S)
    (List.ofFn fun j ↦ ExteriorAlgebra.ι S (s j ⊗ₜ[R] m j)) =
      List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j) := by
    ext j
    simp [ExteriorAlgebra.baseChangeExteriorAlgebraToTensor, ExteriorAlgebra.baseChangeι]
  rw [himages, hprod]
  simpa [ExteriorAlgebra.ιMulti_apply] using
    congrArg (fun x ↦ (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] x)
      (degreeProjection_apply_ιMulti R M i m)

/-- Helper for KoszulComplex baseChangeIso: the linear map on the `i`th exterior power induced
by the inverse-side alternating map. -/
noncomputable def baseChangeIsoInverse (i : ℕ) : ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  alternatingMapLinearEquiv (baseChangeInverseAlternating R M S i)

lemma baseChangeIsoInverse_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeIsoInverse R M S i (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [baseChangeIsoInverse, baseChangeInverseAlternating_apply_tmul]

lemma baseChange_left_inverse (i : ℕ) :
    (baseChangeIsoInverse R M S i).comp (baseChangeIsoForward R M S i) = LinearMap.id := by
  ext m
  have : ((mk R S M) 1) ∘ m = fun j ↦ 1 ⊗ₜ[R] m j := rfl
  simp [baseChangeIsoForward_apply_one_tmul_ιMulti, baseChangeIsoInverse, this,
    baseChangeInverseAlternating_apply_tmul R M S i (fun _ ↦ 1) m]

lemma baseChangeIsoForward_surjective (i : ℕ) :
    Function.Surjective (baseChangeIsoForward R M S i) := by
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
  rw [baseChangeIsoForward_apply_one_tmul_ιMulti]

lemma baseChange_right_inverse (i : ℕ) :
    (baseChangeIsoForward R M S i).comp (baseChangeIsoInverse R M S i) = LinearMap.id := by
  refine LinearMap.ext (fun x ↦ ?_)
  rcases baseChangeIsoForward_surjective R M S i x with ⟨y, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [← LinearMap.comp_apply _ _ y, exteriorPower.baseChange_left_inverse, LinearMap.id_coe, id_eq]

noncomputable def baseChangeIso (i : ℕ) :
    S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) where
  __ := baseChangeIsoForward R M S i
  invFun := baseChangeIsoInverse R M S i
  left_inv x := LinearMap.congr_fun (exteriorPower.baseChange_left_inverse R M S i) x
  right_inv x := LinearMap.congr_fun (exteriorPower.baseChange_right_inverse R M S i) x

lemma baseChangeIso_apply_tmul (i : ℕ) (m : Fin i → M) :
    baseChangeIso R M S i (1 ⊗ₜ[R] (ιMulti R i m)) =
    ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  simp [exteriorPower.baseChangeIso, baseChangeIsoForward_apply_one_tmul_ιMulti]

lemma baseChangeIso_symm_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    (baseChangeIso R M S i).symm (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
    (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [exteriorPower.baseChangeIso, exteriorPower.baseChangeIsoInverse_apply_tmul]

end exteriorPower
