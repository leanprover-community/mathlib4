/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.DirectSum.Module

#align_import linear_algebra.direct_sum.tensor_product from "leanprover-community/mathlib"@"9b9d125b7be0930f564a68f1d73ace10cf46064d"
/-!
# Tensor products of direct sums

This file shows that taking `TensorProduct`s commutes with taking `DirectSum`s in both arguments.

## Main results

* `TensorProduct.directSum`
* `TensorProduct.directSumLeft`
* `TensorProduct.directSumRight`
-/

universe u v₁ v₂ w₁ w₁' w₂ w₂'

section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type u) [CommRing R]

variable {ι₁ : Type v₁} {ι₂ : Type v₂}

variable [DecidableEq ι₁] [DecidableEq ι₂]

variable (M₁ : ι₁ → Type w₁) (M₁' : Type w₁') (M₂ : ι₂ → Type w₂) (M₂' : Type w₂')

variable [∀ i₁, AddCommGroup (M₁ i₁)] [AddCommGroup M₁']

variable [∀ i₂, AddCommGroup (M₂ i₂)] [AddCommGroup M₂']

variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']


/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
protected def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 := by
  -- porting note: entirely rewritten to allow unification to happen one step at a time
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · refine lift ?_
    -- ⊢ (⨁ (i₁ : ι₁), M₁ i₁) →ₗ[R] (⨁ (i₂ : ι₂), M₂ i₂) →ₗ[R] ⨁ (i : ι₁ × ι₂), M₁ i. …
    refine DirectSum.toModule R _ _ fun i₁ => ?_
    -- ⊢ M₁ i₁ →ₗ[R] (⨁ (i₂ : ι₂), M₂ i₂) →ₗ[R] ⨁ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd
    refine @LinearMap.flip R _ R _ R _ R _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    -- ⊢ (⨁ (i₂ : ι₂), M₂ i₂) →ₗ[R] M₁ i₁ →ₗ[R] ⨁ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd
    refine DirectSum.toModule R _ _ fun i₂ => LinearMap.flip <| ?_
    -- ⊢ M₁ i₁ →ₗ[R] M₂ i₂ →ₗ[R] ⨁ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd
    refine curry ?_
    -- ⊢ M₁ i₁ ⊗[R] M₂ i₂ →ₗ[R] ⨁ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd
    exact DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂)
    -- 🎉 no goals
  · refine DirectSum.toModule R _ _ fun i => ?_
    -- ⊢ M₁ i.fst ⊗[R] M₂ i.snd →ₗ[R] (⨁ (i₁ : ι₁), M₁ i₁) ⊗[R] ⨁ (i₂ : ι₂), M₂ i₂
    exact map (DirectSum.lof R _ M₁ i.1) (DirectSum.lof R _ M₂ i.2)
    -- 🎉 no goals
  · refine DirectSum.linearMap_ext R fun ⟨i₁, i₂⟩ => ?_
    -- ⊢ comp (comp (lift (toModule R ι₁ ((⨁ (i₂ : ι₂), M₂ i₂) →ₗ[R] ⨁ (i : ι₁ × ι₂), …
    refine TensorProduct.ext ?_
    -- ⊢ compr₂ (mk R (M₁ (i₁, i₂).fst) (M₂ (i₁, i₂).snd)) (comp (comp (lift (toModul …
    refine LinearMap.ext₂ fun m₁ m₂ => ?_
    -- ⊢ ↑(↑(compr₂ (mk R (M₁ (i₁, i₂).fst) (M₂ (i₁, i₂).snd)) (comp (comp (lift (toM …
    -- porting note: seems much nicer than the `repeat` lean 3 proof.
    simp only [compr₂_apply, comp_apply, id_apply, mk_apply, DirectSum.toModule_lof, map_tmul,
        lift.tmul, flip_apply, curry_apply]
  · -- `(_)` prevents typeclass search timing out on problems that can be solved immediately by
    -- unification
    refine TensorProduct.ext ?_
    -- ⊢ compr₂ (mk R (⨁ (i₁ : ι₁), M₁ i₁) (⨁ (i₂ : ι₂), M₂ i₂)) (comp (toModule R (ι …
    refine @DirectSum.linearMap_ext R _ _ _ _ _ _ _ _ (_) _ _ fun i₁ => ?_
    -- ⊢ comp (compr₂ (mk R (⨁ (i₁ : ι₁), M₁ i₁) (⨁ (i₂ : ι₂), M₂ i₂)) (comp (toModul …
    refine @LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x₁ => ?_
    -- ⊢ ↑(comp (compr₂ (mk R (⨁ (i₁ : ι₁), M₁ i₁) (⨁ (i₂ : ι₂), M₂ i₂)) (comp (toMod …
    refine @DirectSum.linearMap_ext R _ _ _ _ _ _ _ _ (_) _ _ fun i₂ => ?_
    -- ⊢ comp (↑(comp (compr₂ (mk R (⨁ (i₁ : ι₁), M₁ i₁) (⨁ (i₂ : ι₂), M₂ i₂)) (comp  …
    refine LinearMap.ext fun x₂ => ?_
    -- ⊢ ↑(comp (↑(comp (compr₂ (mk R (⨁ (i₁ : ι₁), M₁ i₁) (⨁ (i₂ : ι₂), M₂ i₂)) (com …
    -- porting note: seems much nicer than the `repeat` lean 3 proof.
    simp only [compr₂_apply, comp_apply, id_apply, mk_apply, DirectSum.toModule_lof, map_tmul,
        lift.tmul, flip_apply, curry_apply]
  /- was:

    refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule R _ _ fun i₁ => LinearMap.flip <| DirectSum.toModule R _ _ fun i₂ =>
                LinearMap.flip <| curry <|
                  DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
        (DirectSum.toModule R _ _ fun i => map (DirectSum.lof R _ _ _) (DirectSum.lof R _ _ _)) _
        _ <;>
    [ext ⟨i₁, i₂⟩ x₁ x₂ : 4, ext i₁ i₂ x₁ x₂ : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]
      |rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
  -/

/- alternative with explicit types:
  refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule
            (R := R) (M := M₁) (N := (⨁ i₂, M₂ i₂) →ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2)
            (φ := fun i₁ => LinearMap.flip <|
              DirectSum.toModule (R := R) (M := M₂) (N := ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2)
              (φ := fun i₂ => LinearMap.flip <| curry <|
                  DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))))
        (DirectSum.toModule
          (R := R)
          (M := fun i : ι₁ × ι₂ => M₁ i.1 ⊗[R] M₂ i.2)
          (N := (⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂)
          (φ := fun i : ι₁ × ι₂ => map (DirectSum.lof R _ M₁ i.1) (DirectSum.lof R _ M₂ i.2))) _
        _ <;>
    [ext ⟨i₁, i₂⟩ x₁ x₂ : 4, ext i₁ i₂ x₁ x₂ : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]
      |rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
-/
#align tensor_product.direct_sum TensorProduct.directSum

/-- Tensor products distribute over a direct sum on the left . -/
def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[R] ⨁ i, M₁ i ⊗[R] M₂' :=
  LinearEquiv.ofLinear
    (lift <|
      DirectSum.toModule R _ _ fun i =>
        (mk R _ _).compr₂ <| DirectSum.lof R ι₁ (fun i => M₁ i ⊗[R] M₂') _)
    (DirectSum.toModule R _ _ fun i => rTensor _ (DirectSum.lof R ι₁ _ _))
    (DirectSum.linearMap_ext R fun i =>
      TensorProduct.ext <|
        LinearMap.ext₂ fun m₁ m₂ => by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          -- ⊢ ↑(lift (toModule R ι₁ (M₂' →ₗ[R] ⨁ (i : ι₁), M₁ i ⊗[R] M₂') fun i => compr₂  …
          simp_rw [DirectSum.toModule_lof, rTensor_tmul, lift.tmul, DirectSum.toModule_lof,
            compr₂_apply, mk_apply])
    (TensorProduct.ext <|
      DirectSum.linearMap_ext R fun i =>
        LinearMap.ext₂ fun m₁ m₂ => by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          -- ⊢ ↑(toModule R ι₁ ((⨁ (i₁ : ι₁), M₁ i₁) ⊗[R] M₂') fun i => rTensor M₂' (lof R  …
          simp_rw [lift.tmul, DirectSum.toModule_lof, compr₂_apply,
            mk_apply, DirectSum.toModule_lof, rTensor_tmul])
#align tensor_product.direct_sum_left TensorProduct.directSumLeft

/-- Tensor products distribute over a direct sum on the right. -/
def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[R] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.comm R _ _ ≪≫ₗ directSumLeft R M₂ M₁' ≪≫ₗ
    DFinsupp.mapRange.linearEquiv fun _ => TensorProduct.comm R _ _
#align tensor_product.direct_sum_right TensorProduct.directSumRight

variable {M₁ M₁' M₂ M₂'}

@[simp]
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    TensorProduct.directSum R M₁ M₂ (DirectSum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) := by
  simp [TensorProduct.directSum]
  -- 🎉 no goals
#align tensor_product.direct_sum_lof_tmul_lof TensorProduct.directSum_lof_tmul_lof

@[simp]
theorem directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft R M₁ M₂' (DirectSum.lof R _ _ i x ⊗ₜ[R] y) =
    DirectSum.lof R _ _ i (x ⊗ₜ[R] y) := by
  dsimp only [directSumLeft, LinearEquiv.ofLinear_apply, lift.tmul]
  -- ⊢ ↑(↑(toModule R ι₁ (M₂' →ₗ[R] ⨁ (i : ι₁), M₁ i ⊗[R] M₂') fun i => compr₂ (mk  …
  rw [DirectSum.toModule_lof R i]
  -- ⊢ ↑(↑(compr₂ (mk R (M₁ i) M₂') (lof R ι₁ (fun i => M₁ i ⊗[R] M₂') i)) x) y = ↑ …
  rfl
  -- 🎉 no goals
#align tensor_product.direct_sum_left_tmul_lof TensorProduct.directSumLeft_tmul_lof

@[simp]
theorem directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft R M₁ M₂').symm (DirectSum.lof R _ _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof R _ _ i x ⊗ₜ[R] y := by
  rw [LinearEquiv.symm_apply_eq, directSumLeft_tmul_lof]
  -- 🎉 no goals
#align tensor_product.direct_sum_left_symm_lof_tmul TensorProduct.directSumLeft_symm_lof_tmul

@[simp]
theorem directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight R M₁' M₂ (x ⊗ₜ[R] DirectSum.lof R _ _ i y) =
    DirectSum.lof R _ _ i (x ⊗ₜ[R] y) := by
  dsimp only [directSumRight, LinearEquiv.trans_apply, TensorProduct.comm_tmul]
  -- ⊢ ↑(DFinsupp.mapRange.linearEquiv fun x => TensorProduct.comm R (M₂ x) M₁') (↑ …
  rw [directSumLeft_tmul_lof]
  -- ⊢ ↑(DFinsupp.mapRange.linearEquiv fun x => TensorProduct.comm R (M₂ x) M₁') (↑ …
  exact DFinsupp.mapRange_single (hf := fun _ => rfl)
  -- 🎉 no goals
#align tensor_product.direct_sum_right_tmul_lof TensorProduct.directSumRight_tmul_lof

@[simp]
theorem directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight R M₁' M₂).symm (DirectSum.lof R _ _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y := by
  rw [LinearEquiv.symm_apply_eq, directSumRight_tmul_lof]
  -- 🎉 no goals
#align tensor_product.direct_sum_right_symm_lof_tmul TensorProduct.directSumRight_symm_lof_tmul

end TensorProduct

end Ring
