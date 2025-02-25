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

open LinearMap

include fg in
private lemma projection_inclusion1 : (g0.lcomp R P).comp (f0.lcomp R P) =
    LinearMap.id := by
  ext f x
  simp only [coe_comp, Function.comp_apply, lcomp_apply, id_coe, id_eq]
  exact congr(f ($fg x))

include fg fg' in
private lemma tensor_inclusion1_projection1 :
  (TensorProduct.map (g0.lcomp R P) (g0'.lcomp R Q)).comp
    (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q)) = LinearMap.id := by
  simp [← TensorProduct.map_comp, projection_inlusion1 R M P M' f0 g0 fg,
    projection_inlusion1 R N Q N' f0' g0' fg']

include g0 g0' fg fg' in
private lemma tensor_inclusion1_inj: Function.Injective
  (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q)) := by
  exact Function.LeftInverse.injective (g := (TensorProduct.map (g0.lcomp R P) (g0'.lcomp R Q)))
    <| DFunLike.congr_fun <| tensor_inclusion1_projection1 R M N P Q _ _ f0 g0 fg f0' g0' fg'

variable {M N M' N'} in
include fg fg' in
private lemma projection2_inclusion2 : (TensorProduct.map f0 f0').comp (TensorProduct.map g0 g0') =
    LinearMap.id (R := R) (M := M ⊗[R] N) := by
  simp [← TensorProduct.map_comp, fg, fg']

include fg fg' in
private lemma projection2_inclusion2_apply (x : M ⊗[R] N): (TensorProduct.map f0 f0')
    (TensorProduct.map g0 g0' x) = x :=
  DFunLike.congr_fun (projection2_inclusion2 R f0 g0 fg f0' g0' fg') x

include fg fg' in
private lemma tensor_projection2_inclusion2 : ((TensorProduct.map g0 g0').lcomp _ _).comp
    ((TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q)) =
    LinearMap.id (R := R) (M := M ⊗[R] N →ₗ[R] P ⊗[R] Q) := by
  ext f : 1
  simp [LinearMap.lcomp_apply', LinearMap.comp_assoc,
    projection2_inclusion2 R f0 g0 fg f0' g0' fg']

include g0 g0' fg fg' in
private lemma tensor_inclusion2_inj : Function.Injective
  ((TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q)) := by
  exact Function.LeftInverse.injective (g := (TensorProduct.map g0 g0').lcomp _ _)
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
private lemma comm_square2: (homTensorHomEquiv R M' N' P Q).toLinearMap ∘ₗ
    (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q)) =
    ((TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q)) ∘ₗ
    TensorProduct.homTensorHomMap R M N P Q := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

private lemma comm_square2_apply (f : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)):
  (homTensorHomEquiv R M' N' P Q).toLinearMap
    (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q) f) =
    (TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q) (TensorProduct.homTensorHomMap R M N P Q f) :=
  DFunLike.congr_fun (comm_square2 R M N P Q M' N' f0 f0') f

include f0 f0' g0 g0' fg fg' in
lemma homTensorHomMap_inj : Function.Injective
  (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Injective.of_comp (f := (TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q))
  rw [← LinearMap.coe_comp, ← comm_square2]
  exact Function.Injective.comp (f := TensorProduct.map _ _)
    (homTensorHomEquiv R M' N' P Q).injective <|
    tensor_inclusion1_inj _ _ _ _ _ _ _ _ _ fg _ _ fg'

private lemma comm_square3 : (homTensorHomEquiv R _ _ _ _).toLinearMap ∘ₗ
    (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q)) ∘ₗ
    (TensorProduct.map (g0.lcomp R P) (g0'.lcomp R Q)) =
    (TensorProduct.map f0 f0').lcomp _ _ ∘ₗ (TensorProduct.map g0 g0').lcomp _ _ ∘ₗ
    (homTensorHomEquiv R _ _ _ _).toLinearMap := by
  ext f g : 4
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  simp

private lemma comm_square3_apply (f : (M' →ₗ[R] P) ⊗[R] (N' →ₗ[R] Q)):
    (homTensorHomEquiv R _ _ _ _) (TensorProduct.map (f0.lcomp R P) (f0'.lcomp R Q)
    ((TensorProduct.map (g0.lcomp R P) (g0'.lcomp R Q)) f)) =
    (TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q) ((TensorProduct.map g0 g0').lcomp _ _
    (homTensorHomEquiv R _ _ _ _ f)) :=
  DFunLike.congr_fun (comm_sqaure3 R M N P Q M' N' f0 g0 f0' g0') f

include fg fg' in
private lemma comm_square4: TensorProduct.homTensorHomMap R M N P Q ∘ₗ
    (TensorProduct.map (g0.lcomp R P) (g0'.lcomp R Q)) ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ
    (TensorProduct.map f0 f0').lcomp R (P ⊗[R] Q) =
    LinearMap.id (M := (M ⊗[R] N) →ₗ[R] P ⊗[R] Q) := by
  apply LinearMap.ext
  intro fgfg
  simp only [LinearMap.comp_apply]
  apply tensor_inclusion2_inj R M N P Q M' N' f0 g0 fg f0' g0' fg'
  rw [← comm_square2_apply, LinearEquiv.coe_toLinearMap, comm_square3_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, id_coe, id_eq]
  apply LinearMap.ext
  simp [projection2_inclusion2_apply R M N M' N' f0 g0 fg f0' g0' fg']

include M' N' f0 f0' g0 g0' fg fg' in
lemma homTensorHomMap_surj: Function.Surjective (TensorProduct.homTensorHomMap R M N P Q) := by
  apply Function.Surjective.of_comp (g := (TensorProduct.map (g0.lcomp _ _) (g0'.lcomp _ _)) ∘ₗ
    (homTensorHomEquiv R _ _ _ _).symm.toLinearMap ∘ₗ (TensorProduct.map f0 f0').lcomp _ _)
  rw [← LinearMap.coe_comp, comm_square4 R M N P Q M' N' f0 g0 fg f0' g0' fg']
  exact Function.RightInverse.surjective (congrFun rfl)

variable [Module.Projective R M] [Module.Projective R N] [Module.Finite R M] [Module.Finite R N]

lemma homTensorHomMap_bij: Function.Bijective (TensorProduct.homTensorHomMap R M N P Q) := by
  obtain ⟨n1, f0, g0, hf, hg, fg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  obtain ⟨n2, f0', g0', hf', hg', fg'⟩ := Module.Finite.exists_comp_eq_id_of_projective R N
  exact ⟨homTensorHomMap_inj R M N P Q (Fin n1 → R) (Fin n2 → R) _ _ fg _ _ fg',
    homTensorHomMap_surj R M N P Q (Fin n1 → R) (Fin n2 → R) _ _ fg _ _ fg'⟩

/-- `Hom (M, P) ⊗ Hom (N, Q)` is linearly equivalent to `Hom(M ⊗ N, P ⊗ Q)` via the map
`TensorProduct.homTensorHomMap`, this could also be seen as a generalisation of
`homTensorHomEquiv`. -/
@[simps!]
def Module.Hom.Tensor : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P ⊗[R] Q) :=
  LinearEquiv.ofBijective (TensorProduct.homTensorHomMap R M N P Q) (homTensorHomMap_bij R M N P Q)
