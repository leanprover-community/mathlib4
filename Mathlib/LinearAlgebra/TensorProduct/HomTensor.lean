/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Andrew Yang
-/
import Mathlib.LinearAlgebra.Contraction

/-!

This file proves that for `M` and `N` being finitely generated projective
modules over a commutative ring `R`, then the tensor product of the hom module
from `M` to `P` tensor the one from `N` to `Q` for `P`, `Q` being arbitrary
`R`-modules is isomorphic to the hom module from `M ⊗ N` to `P ⊗ Q` as modules.

## Main results
* `Module.End.Tensor`: The tensor product of the hom modules is isomorphic to the
  hom module of the tensor product.

# Tags
tensor product, module, hom
-/

suppress_compilation

open scoped TensorProduct

variable (R : Type*) [CommRing R] (M N P Q: Type*) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Projective R M]
  [Module.Projective R N] [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]

private abbrev nn : ℕ := (Module.Finite.exists_comp_eq_id_of_projective R M).choose

private abbrev f0 : (Fin (nn R M) → R) →ₗ[R] M :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose

private abbrev g0 : M →ₗ[R] Fin (nn R M) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose

lemma f0_surj : Function.Surjective (f0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.1

lemma g0_inj : Function.Injective (g0 R M) :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.1

lemma fg : (f0 R M) ∘ₗ (g0 R M) = LinearMap.id :=
  (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.2

/-- the map from `Hom(M, P)` to `Hom(Rⁿ, P)` induced from `M` being finitely generated projecive.-/
abbrev inclusion1 : (M →ₗ[R] P) →ₗ[R] ((Fin (nn R M) → R) →ₗ[R] P) where
  toFun := fun f ↦ f.comp (f0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

/-- the map from `Hom(Rⁿ, P)` to `Hom(M, P)` induced from `M` being finitely generated projecive.-/
abbrev projection1 : ((Fin (nn R M) → R) →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun := fun f ↦ f.comp (g0 R M)
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

/-- `Hom(M, P) ⊗ Hom(N, Q) →ₗ[R] Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q)` -/
abbrev tensor_inclusion1 : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R]
  ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q) :=
  TensorProduct.map (inclusion1 R M P) (inclusion1 R N Q)

/-- `Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) →ₗ[R] Hom(M, P) ⊗ Hom(N, Q)` -/
abbrev tensor_projection1 := TensorProduct.map (projection1 R M P) (projection1 R N Q)

lemma projection_inlusion1 : (projection1 R M P).comp (inclusion1 R M P) = LinearMap.id := by
  ext f : 1
  simp [LinearMap.comp_assoc, fg]

lemma tensor_inclusion1_projection1 : (tensor_projection1 R M N P Q).comp
    (tensor_inclusion1 R M N P Q) = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1]

lemma tensor_inclusion1_projection1_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
    (tensor_projection1 R M N P Q) ((tensor_inclusion1 R M N P Q) x) = x :=
  DFunLike.congr_fun (tensor_inclusion1_projection1 R M N P Q) x

lemma tensor_inclusion1_inj: Function.Injective (tensor_inclusion1 R M N P Q) := by
  exact Function.LeftInverse.injective (g := tensor_projection1 R M N P Q)
    <| DFunLike.congr_fun <| tensor_inclusion1_projection1 R M N P Q

variable {R M N} in
private abbrev inclusion2 : M ⊗[R] N →ₗ[R] (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) :=
  TensorProduct.map (g0 R M) (g0 R N)

variable {R M N} in
private abbrev projection2 : (Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (f0 R M) (f0 R N)

variable {M N} in
/-- The injection from `Hom(M ⊗ N, P ⊗ Q)` to `Hom (Rⁿ ⊗ Rᵐ, P ⊗ Q)`.-/
abbrev tensor_inclusion2 : (M ⊗[R] N →ₗ[R] P ⊗[R] Q) →ₗ[R]
    ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp projection2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

variable {M N} in
/-- The projection from `Hom (Rⁿ ⊗ Rᵐ, P ⊗ Q)` to `Hom(M ⊗ N, P ⊗ Q)`.-/
abbrev tensor_projection2 : ((Fin (nn R M) → R) ⊗[R] (Fin (nn R N) → R) →ₗ[R]
    P ⊗[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) where
  toFun := fun f ↦ f.comp inclusion2
  map_add' := by simp [LinearMap.add_comp]
  map_smul' := by simp [LinearMap.smul_comp]

lemma projection2_inclusion2 : (projection2).comp (inclusion2) =
    LinearMap.id (R := R) (M := M ⊗[R] N) :=
  by simp [← TensorProduct.map_comp, fg]

lemma projection2_inclusion2_apply (x : M ⊗[R] N): (projection2) ((inclusion2) x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R M N) x

lemma tensor_projection2_inclusion2 : (tensor_projection2 R P Q).comp (tensor_inclusion2 R P Q) =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.comp_assoc, projection2_inclusion2]

lemma tensor_inclusion2_inj : Function.Injective (tensor_inclusion2 R (M := M) (N := N) P Q) := by
  exact Function.LeftInverse.injective (g := tensor_projection2 R P Q)
    <| DFunLike.congr_fun <| tensor_projection2_inclusion2 R M N P Q

/--
```
           TensorProduct.homTensorHomMap
Hom(M, P) ⊗ Hom(N, Q) ---------------> Hom(M ⊗ N, P ⊗ Q)
    |       |                             |      |
 i  |       |  j                       i' |      |  j'
    |       |                             |      |
    |       |                             |      |
Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) -------------> Hom(Rⁿ ⊗ Rᵐ, P ⊗ Q)
```
-/
lemma comm_square2: (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q =
    tensor_inclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap R M N P Q := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
  (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).toLinearMap
    (tensor_inclusion1 R M N P Q f) =
    tensor_inclusion2 R P Q (TensorProduct.homTensorHomMap R M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q) f

lemma homTensorHomMap_inj : Function.Injective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Injective.of_comp (f := tensor_inclusion2 R P Q)
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := tensor_inclusion1 R M N P Q)
    (homTensorHomEquiv R (Fin (nn R M) → R) (Fin (nn R N) → R) P Q).injective <|
    tensor_inclusion1_inj R M N P Q

lemma comm_sqaure3: (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q ∘ₗ tensor_projection1 R M N P Q = tensor_inclusion2 R P Q ∘ₗ
    tensor_projection2 R P Q ∘ₗ (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square3_apply (f : ((Fin (nn R M) → R) →ₗ[R] P) ⊗[R] ((Fin (nn R N) → R) →ₗ[R] Q)):
    (homTensorHomEquiv R _ _ _ _) (tensor_inclusion1 R M N P Q (tensor_projection1 R M N P Q f)) =
    tensor_inclusion2 R P Q (tensor_projection2 R P Q (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_sqaure3 R M N P Q) f

lemma comm_square1: tensor_projection1 R M N P Q ∘ₗ
  (homTensorHomEquiv R _ _ P Q).symm.toLinearMap ∘ₗ
    tensor_inclusion2 R P Q ∘ₗ TensorProduct.homTensorHomMap R M N P Q =
    LinearMap.id (R := R) (M := (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):= by
  rw [← comm_square2]
  apply LinearMap.ext
  simp [-homTensorHomEquiv_toLinearMap, -homTensorHomEquiv_apply,
    tensor_inclusion1_projection1_apply]

lemma comm_square4: TensorProduct.homTensorHomMap R M N P Q ∘ₗ tensor_projection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensor_inclusion2 R P Q =
    LinearMap.id (R := R) (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensor_inclusion2_inj
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp [LinearMap.comp_assoc]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply]

lemma homTensorHomMap_surj: Function.Surjective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Surjective.of_comp (g := (tensor_projection1 R M N P Q ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensor_inclusion2 R P Q))
  rw [← LinearMap.coe_comp, comm_square4]
  exact Function.RightInverse.surjective (congrFun rfl)

/-- `Hom (M, P) ⊗ Hom (N, Q)` is linearly equivalent to `Hom(M ⊗ N, P ⊗ Q)` via the map
  `TensorProduct.homTensorHomMap`, this could also be seen as a generalisation of
  `homTensorHomEquiv`. -/
abbrev Module.End.Tensor: (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  LinearEquiv.ofBijective (TensorProduct.homTensorHomMap R M N P Q)
  ⟨homTensorHomMap_inj R M N P Q, homTensorHomMap_surj R M N P Q⟩
