/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Andrew Yang
-/
import Mathlib.LinearAlgebra.Contraction

/-!

This file proves that for `M` and `N` finitely generated projective
modules over a commutative ring `R`, the tensor product of the hom module
from `M` to `P` and the one from `N` to `Q` for `P`, `Q` being arbitrary
`R`-modules is isomorphic to the hom module from `M ⊗ N` to `P ⊗ Q` as modules.

## Main results
* `Module.Hom.Tensor`: The tensor product of the hom modules is isomorphic to the
  hom module of the tensor product.

# Tags
tensor product, module, hom
-/

suppress_compilation

open scoped TensorProduct

variable (R : Type*) [CommRing R] (M N P Q M' N': Type*) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

variable (f0 : M' →ₗ[R] M) (g0 : M →ₗ[R] M') (fg : f0.comp g0 = LinearMap.id)
  (f0' : N' →ₗ[R] N) (g0' : N →ₗ[R] N') (fg' : f0'.comp g0' = LinearMap.id)


-- lemma f0_surj : Function.Surjective (f0 R M) :=
--   (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.1

-- lemma g0_inj : Function.Injective (g0 R M) :=
--   (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.1

-- lemma fg : (f0 R M) ∘ₗ (g0 R M) = LinearMap.id :=
--   (Module.Finite.exists_comp_eq_id_of_projective R M).choose_spec.choose_spec.choose_spec|>.2.2

/-- the map from `Hom(M, P)` to `Hom(Rⁿ, P)` induced from `M` being finitely generated projecive.-/
abbrev inclusion1 : (M →ₗ[R] P) →ₗ[R] (M' →ₗ[R] P) := LinearMap.lcomp _ _ f0

/-- the map from `Hom(Rⁿ, P)` to `Hom(M, P)` induced from `M` being finitely generated projecive.-/
abbrev projection1 : (M' →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) := LinearMap.lcomp _ _ g0

/-- `Hom(M, P) ⊗ Hom(N, Q) →ₗ[R] Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q)` -/
abbrev tensor_inclusion1 : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) →ₗ[R]
  (M' →ₗ[R] P) ⊗[R] (N' →ₗ[R] Q) :=
  TensorProduct.map (inclusion1 R M P M' f0) (inclusion1 R N Q N' f0')

/-- `Hom(Rⁿ, P) ⊗ Hom(Rᵐ, Q) →ₗ[R] Hom(M, P) ⊗ Hom(N, Q)` -/
abbrev tensor_projection1 := TensorProduct.map (projection1 R M P M' g0) (projection1 R N Q N' g0')

include fg in
lemma projection_inlusion1 : (projection1 R M P M' g0).comp (inclusion1 R M P M' f0) =
    LinearMap.id := by
  ext f x
  simp [LinearMap.comp_assoc]
  exact congr(f ($fg x))

include fg fg' in
lemma tensor_inclusion1_projection1 : (tensor_projection1 R M N P Q M' N' g0 g0').comp
    (tensor_inclusion1 R M N P Q M' N' f0 f0') = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1 R M P M' f0 g0 fg,
    projection_inlusion1 R N Q N' f0' g0' fg']

include fg fg' in
lemma tensor_inclusion1_projection1_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
    (tensor_projection1 R M N P Q _ _ g0 g0') ((tensor_inclusion1 R M N P Q _ _ f0 f0') x) = x :=
  DFunLike.congr_fun (tensor_inclusion1_projection1 R M N P Q _ _ f0 g0 fg f0' g0' fg') x

include g0 g0' fg fg' in
lemma tensor_inclusion1_inj: Function.Injective (tensor_inclusion1 R M N P Q M' N' f0 f0') := by
  exact Function.LeftInverse.injective (g := tensor_projection1 R M N P Q _ _ g0 g0')
    <| DFunLike.congr_fun <| tensor_inclusion1_projection1 R M N P Q _ _ f0 g0 fg f0' g0' fg'

variable {R M N} in
private abbrev inclusion2 := TensorProduct.map g0 g0'

variable {R M N} in
private abbrev projection2 := TensorProduct.map f0 f0'

variable {M N M' N'} in
/-- The injection from `Hom(M ⊗ N, P ⊗ Q)` to `Hom (Rⁿ ⊗ Rᵐ, P ⊗ Q)`.-/
abbrev tensor_inclusion2 : (M ⊗[R] N →ₗ[R] P ⊗[R] Q) →ₗ[R]
    (M' ⊗[R] N' →ₗ[R] P ⊗[R] Q) := LinearMap.lcomp _ _ (inclusion2 _ _ f0 f0')

variable {M N M' N'} in
/-- The projection from `Hom (Rⁿ ⊗ Rᵐ, P ⊗ Q)` to `Hom(M ⊗ N, P ⊗ Q)`.-/
abbrev tensor_projection2 : (M' ⊗[R] N' →ₗ[R] P ⊗[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  LinearMap.lcomp R _ (projection2 _ _ g0 g0')

include fg fg' in
lemma projection2_inclusion2 : (projection2 M' N' f0 f0').comp (inclusion2 M' N' g0 g0') =
    LinearMap.id (R := R) (M := M ⊗[R] N) := by
  simp [← TensorProduct.map_comp, fg, fg']

include fg fg' in
lemma projection2_inclusion2_apply (x : M ⊗[R] N): (projection2 _ _ f0 f0')
    (inclusion2 _ _ g0 g0' x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R M N _ _ f0 g0 fg f0' g0' fg') x

include fg fg' in
lemma tensor_projection2_inclusion2 : (tensor_projection2 R P Q g0 g0').comp
    (tensor_inclusion2 R P Q f0 f0') =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.lcomp_apply', LinearMap.comp_assoc,
    projection2_inclusion2 R M N M' N' f0 g0 fg f0' g0' fg']

include g0 g0' fg fg' in
lemma tensor_inclusion2_inj : Function.Injective (tensor_inclusion2 R P Q f0 f0') := by
  exact Function.LeftInverse.injective (g := tensor_projection2 R P Q g0 g0')
    <| DFunLike.congr_fun (tensor_projection2_inclusion2 R M N P Q _ _ f0 g0 fg f0' g0' fg')

variable [Module.Free R M'] [Module.Finite R M'] [Module.Free R N'] [Module.Finite R N']
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
lemma comm_square2: (homTensorHomEquiv R M' N' P Q).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q M' N' f0 f0' =
    tensor_inclusion2 R P Q f0 f0' ∘ₗ TensorProduct.homTensorHomMap R M N P Q := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
  (homTensorHomEquiv R M' N' P Q).toLinearMap
    (tensor_inclusion1 R M N P Q M' N' f0 f0' f) =
    tensor_inclusion2 R P Q f0 f0' (TensorProduct.homTensorHomMap R M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q M' N' f0 f0') f

include f0 f0' g0 g0' fg fg' in
lemma homTensorHomMap_inj : Function.Injective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Injective.of_comp (f := tensor_inclusion2 R P Q f0 f0')
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := tensor_inclusion1 R M N P Q _ _ f0 f0')
    (homTensorHomEquiv R M' N' P Q).injective <|
    tensor_inclusion1_inj R M N P Q _ _ f0 g0 fg f0' g0' fg'

lemma comm_sqaure3: (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    tensor_inclusion1 R M N P Q M' N' f0 f0' ∘ₗ tensor_projection1 R M N P Q M' N' g0 g0' =
    tensor_inclusion2 R P Q f0 f0'∘ₗ tensor_projection2 R P Q g0 g0' ∘ₗ
    (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

lemma comm_square3_apply (f : (M' →ₗ[R] P) ⊗[R] (N' →ₗ[R] Q)):
    (homTensorHomEquiv R _ _ _ _) (tensor_inclusion1 R M N P Q M' N' f0 f0'
    (tensor_projection1 R M N P Q M' N' g0 g0' f)) =
    tensor_inclusion2 R P Q f0 f0' (tensor_projection2 R P Q g0 g0'
    (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_sqaure3 R M N P Q M' N' f0 g0 f0' g0') f

include fg fg' in
lemma comm_square4: TensorProduct.homTensorHomMap R M N P Q ∘ₗ
    tensor_projection1 R M N P Q M' N' g0 g0' ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ
    tensor_inclusion2 R P Q f0 f0' =
    LinearMap.id (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensor_inclusion2_inj R M N P Q M' N' f0 g0 fg f0' g0' fg'
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp [LinearMap.comp_assoc]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply R M N M' N' f0 g0 fg f0' g0' fg']

include M' N' f0 f0' g0 g0' fg fg' in
lemma homTensorHomMap_surj: Function.Surjective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Surjective.of_comp (g := (tensor_projection1 R M N P Q M' N' g0 g0' ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ tensor_inclusion2 R P Q f0 f0'))
  rw [← LinearMap.coe_comp, comm_square4 R M N P Q M' N' f0 g0 fg f0' g0' fg']
  exact Function.RightInverse.surjective (congrFun rfl)

variable [Module.Projective R M] [Module.Projective R N] [Module.Finite R M] [Module.Finite R N]

lemma homTensorHomMap_bij: Function.Bijective (TensorProduct.homTensorHomMap R M N P Q) := by
  obtain ⟨n1, f0, g0, hf, hg, fg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨n2, f0', g0', hf', hg', fg'⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  exact ⟨homTensorHomMap_inj R M N P Q (Fin n1 → R) (Fin n2 → R) f0 g0 fg f0' g0' fg',
    homTensorHomMap_surj R M N P Q (Fin n1 → R) (Fin n2 → R) f0 g0 fg f0' g0' fg'⟩

/-- `Hom (M, P) ⊗ Hom (N, Q)` is linearly equivalent to `Hom(M ⊗ N, P ⊗ Q)` via the map
  `TensorProduct.homTensorHomMap`, this could also be seen as a generalisation of
  `homTensorHomEquiv`. -/
abbrev Module.Hom.Tensor: (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  LinearEquiv.ofBijective (TensorProduct.homTensorHomMap R M N P Q) (homTensorHomMap_bij R M N P Q)
