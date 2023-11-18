/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.DirectLimit

/-!
# Tensor product and direct limits commute with each other.
Given a family of `R`-modules `Gᵢ` with a family of compatible `R`-linear maps `fᵢⱼ : Gᵢ → Gⱼ` for
every `i ≤ j` and another `R`-module `M`, we have `(limᵢ Gᵢ) ⊗ M` and `lim (Gᵢ ⊗ M)` are isomorphic
as `R`-modules.

-/

open TensorProduct Module.DirectLimit

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type w}

namespace Module

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- limᵢ (Gᵢ ⊗ M) -/
local notation "Lim_G_tensor" =>
  (DirectLimit (G · ⊗[R] M) fun i j h => LinearMap.rTensor M (f _ _ h))

/-- limᵢ Gᵢ -/
local notation "Lim_G" => (DirectLimit G f)

/--
the map `limᵢ (Gᵢ ⊗ M) → (limᵢ Gᵢ) ⊗ M` induced by the family of maps `Gᵢ ⊗ M → (limᵢ Gᵢ) ⊗ M`
given by `gᵢ ⊗ m ↦ [gᵢ] ⊗ m`.
-/
noncomputable def directLimitOfTensorProductToTensorProductWithDirectLimit :
    Lim_G_tensor →ₗ[R] Lim_G ⊗[R] M :=
  lift _ _ _ _ (fun _ => (of _ _ _ _ _).rTensor M)
    fun _ _ _ x => by refine' x.induction_on _ _ _ <;> aesop

variable {M} in
@[simp] lemma directLimitOfTensorProductToTensorProductWithDirectLimit_apply_of_tmul
    {i : ι} (g : G i) (m : M) :
    directLimitOfTensorProductToTensorProductWithDirectLimit f M (of _ _ _ _ i (g ⊗ₜ m)) =
    (of _ _ _ _ i g : Lim_G) ⊗ₜ m :=
  lift_of (G := (G · ⊗[R] M)) _ _ (g ⊗ₜ m)

/--
the map `(limᵢ Gᵢ) ⊗ M → limᵢ (Gᵢ ⊗ M)` from the bilinear map `limᵢ Gᵢ → M → limᵢ (Gᵢ ⊗ M)` given
by the family of maps `Gᵢ → M → limᵢ (Gᵢ ⊗ M)` where `gᵢ ↦ m ↦ [gᵢ ⊗ m]`

-/
noncomputable def tensorProductWithDirectLimitToDirectLimitOfTensorProduct :
    Lim_G ⊗[R] M →ₗ[R] Lim_G_tensor :=
  TensorProduct.lift <| DirectLimit.lift _ _ _ _
    (fun i =>
      { toFun := (of R ι _ (fun i j h => (f _ _ h).rTensor M) i ∘ₗ TensorProduct.mk R _ _ ·)
        map_add' := by aesop
        map_smul' := by aesop })
    fun _ _ _ g => FunLike.ext _ _ (of_f (G := (G · ⊗[R] M)) (x := g ⊗ₜ ·))

variable {M} in
@[simp] lemma tensorProductWithDirectLimitToDirectLimitOfTensorProduct_apply_of_tmul
    {i : ι} (g : G i) (m : M) :
    (tensorProductWithDirectLimitToDirectLimitOfTensorProduct f M <|
      (of _ _ _ _ i g : Lim_G) ⊗ₜ m) =
    (of _ _ _ _ i (g ⊗ₜ m) : Lim_G_tensor) := by
  rw [tensorProductWithDirectLimitToDirectLimitOfTensorProduct, lift.tmul, lift_of]
  rfl

variable [IsDirected ι (· ≤ ·)]

/--
`limᵢ (Gᵢ ⊗ M)` and `(limᵢ Gᵢ) ⊗ M` are isomorphic as modules
-/
@[simps!]
noncomputable def directLimitCommutesTensorProduct :
    Lim_G_tensor ≃ₗ[R] Lim_G ⊗[R] M := by
  refine LinearEquiv.ofLinear
    (directLimitOfTensorProductToTensorProductWithDirectLimit f M)
    (tensorProductWithDirectLimitToDirectLimitOfTensorProduct f M) ?_ ?_
    <;> cases isEmpty_or_nonempty ι
  · ext; apply Subsingleton.elim
  · exact ext (FunLike.ext _ _ fun g => FunLike.ext _ _ fun _ => g.induction_on <| by aesop)
  · ext; apply Subsingleton.elim
  · refine FunLike.ext _ _ fun x => x.induction_on fun i g => g.induction_on ?_ ?_ ?_ <;> aesop

end Module
