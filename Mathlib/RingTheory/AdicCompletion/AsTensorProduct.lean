/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.TensorProduct.Basic

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show

- it is an isomorphism if `M = R^n`.
- it is surjective, if `M` is a finite `R`-module.
- it is an isomorphism if `M` is a finite `R`-module and `R` is Noetherian.

-/

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace AdicCompletion

private def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearMap.lsmul_apply, RingHom.id_apply, LinearMap.smul_apply]
    rw [smul_eq_mul, mul_smul]

@[simp]
private theorem ofTensorProductBil_apply_apply (r : AdicCompletion I R) (x : M) :
    ((AdicCompletion.ofTensorProductBil I M) r) x = r • (of I M) x :=
  rfl

open TensorProduct

noncomputable def ofTensorProduct :
    AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift (ofTensorProductBil I M)

@[simp]
theorem ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  simp [ofTensorProduct]

def ofTensorProductInvOfFin (n : ℕ) :
    AdicCompletion I (Fin n → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (Fin n → R) :=
  let f := piEquivFin I n
  sorry

theorem ofTensorProductEquivOfFin (n : ℕ) :
    AdicCompletion I R ⊗[R] (Fin n → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (Fin n → R) :=
  LinearEquiv.ofLinear
    (ofTensorProduct I (Fin n → R))
    sorry
    sorry
    sorry

theorem ofTensorProduct_bijective_of_fin (n : ℕ) :
    Function.Bijective (ofTensorProduct I (Fin n → R)) := by
  --show Function.Bijective (ofTensorProductEquivOfFin I n).toLinearMap
  sorry

theorem ofTensorProduct_surjective_of_fg [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := p.adicCompletion I ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
    rfl
  have hg : Function.Surjective g := by
    dsimp [g]
    apply Function.Surjective.comp
    sorry
    exact (ofTensorProduct_bijective_of_fin I n).surjective
  apply Function.Surjective.of_comp
  show Function.Surjective f
  rw [hfg]
  exact hg
