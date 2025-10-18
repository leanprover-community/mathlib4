/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor product and direct limits commute with each other.

Given a family of `R`-modules `Gᵢ` with a family of compatible `R`-linear maps `fᵢⱼ : Gᵢ → Gⱼ` for
every `i ≤ j` and another `R`-module `M`, we have `(limᵢ Gᵢ) ⊗ M` and `lim (Gᵢ ⊗ M)` are isomorphic
as `R`-modules.

## Main definitions:

* `TensorProduct.directLimitLeft : DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M)`
* `TensorProduct.directLimitRight : M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f)`

-/

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommSemiring R]
variable {ι : Type*}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type*}
variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type*) [AddCommMonoid M] [Module R M]

-- alluding to the notation in `CategoryTheory.Monoidal`
local notation M " ◁ " f => fun i j h ↦ LinearMap.lTensor M (f _ _ h)
local notation f " ▷ " N => fun i j h ↦ LinearMap.rTensor N (f _ _ h)

namespace TensorProduct

/--
the map `limᵢ (Gᵢ ⊗ M) → (limᵢ Gᵢ) ⊗ M` induced by the family of maps `Gᵢ ⊗ M → (limᵢ Gᵢ) ⊗ M`
given by `gᵢ ⊗ m ↦ [gᵢ] ⊗ m`.
-/
noncomputable def fromDirectLimit :
    DirectLimit (G · ⊗[R] M) (f ▷ M) →ₗ[R] DirectLimit G f ⊗[R] M :=
  Module.DirectLimit.lift _ _ _ _ (fun _ ↦ (of _ _ _ _ _).rTensor M)
    fun _ _ _ x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop

variable {M} in
@[simp] lemma fromDirectLimit_of_tmul {i : ι} (g : G i) (m : M) :
    fromDirectLimit f M (of _ _ _ _ i (g ⊗ₜ m)) = (of _ _ _ f i g) ⊗ₜ m :=
  lift_of (G := (G · ⊗[R] M)) _ _ (g ⊗ₜ m)

/--
the map `(limᵢ Gᵢ) ⊗ M → limᵢ (Gᵢ ⊗ M)` from the bilinear map `limᵢ Gᵢ → M → limᵢ (Gᵢ ⊗ M)` given
by the family of maps `Gᵢ → M → limᵢ (Gᵢ ⊗ M)` where `gᵢ ↦ m ↦ [gᵢ ⊗ m]`
-/
noncomputable def toDirectLimit : DirectLimit G f ⊗[R] M →ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  TensorProduct.lift <| Module.DirectLimit.lift _ _ _ _
    (fun i ↦
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h ↦ (f _ _ h).rTensor M) i))
    fun _ _ _ g ↦ DFunLike.ext _ _ (of_f (G := (G · ⊗[R] M)) (x := g ⊗ₜ ·))

variable {M} in
@[simp] lemma toDirectLimit_tmul_of
    {i : ι} (g : G i) (m : M) :
    (toDirectLimit f M <| (of _ _ G f i g) ⊗ₜ m) = (of _ _ _ _ i (g ⊗ₜ m)) := by
  rw [toDirectLimit, lift.tmul, lift_of]
  rfl

attribute [local ext] TensorProduct.ext in
/--
`limᵢ (Gᵢ ⊗ M)` and `(limᵢ Gᵢ) ⊗ M` are isomorphic as modules
-/
noncomputable def directLimitLeft :
    DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  LinearEquiv.ofLinear (toDirectLimit f M) (fromDirectLimit f M) (by ext; simp) (by ext; simp)

@[simp] lemma directLimitLeft_tmul_of {i : ι} (g : G i) (m : M) :
    directLimitLeft f M (of _ _ _ _ _ g ⊗ₜ m) = of _ _ _ (f ▷ M) _ (g ⊗ₜ m) :=
  toDirectLimit_tmul_of f g m

@[simp] lemma directLimitLeft_symm_of_tmul {i : ι} (g : G i) (m : M) :
    (directLimitLeft f M).symm (of _ _ _ _ _ (g ⊗ₜ m)) = of _ _ _ f _ g ⊗ₜ m :=
  fromDirectLimit_of_tmul f g m

lemma directLimitLeft_rTensor_of {i : ι} (x : G i ⊗[R] M) :
    directLimitLeft f M (LinearMap.rTensor M (of ..) x) = of _ _ _ (f ▷ M) _ x :=
  x.induction_on (by simp) (by simp+contextual) (by simp+contextual)

/--
`M ⊗ (limᵢ Gᵢ)` and `limᵢ (M ⊗ Gᵢ)` are isomorphic as modules
-/
noncomputable def directLimitRight :
    M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f) :=
  TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ ↦ TensorProduct.comm _ _ _)
      (fun i j h ↦ TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)

@[simp] lemma directLimitRight_tmul_of {i : ι} (m : M) (g : G i) :
    directLimitRight f M (m ⊗ₜ of _ _ _ _ _ g) = of _ _ _ _ i (m ⊗ₜ g) := by
  simp [directLimitRight, congr_apply_of]

@[simp] lemma directLimitRight_symm_of_tmul {i : ι} (m : M) (g : G i) :
    (directLimitRight f M).symm (of _ _ _ _ _ (m ⊗ₜ g)) = m ⊗ₜ of _ _ _ f _ g := by
  simp [directLimitRight, congr_symm_apply_of]

variable [DirectedSystem G (f · · ·)]

instance : DirectedSystem (G · ⊗[R] M) (f ▷ M) where
  map_self i x := by
    convert LinearMap.rTensor_id_apply M (G i) x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ _ _ x := by
    convert ← (LinearMap.rTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

instance : DirectedSystem (M ⊗[R] G ·) (M ◁ f) where
  map_self i x := by
    convert LinearMap.lTensor_id_apply M _ x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ h₁ h₂ x := by
    convert ← (LinearMap.lTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

end TensorProduct
