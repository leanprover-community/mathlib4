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

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommRing R]
variable {ι : Type*}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type*}

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type*) [AddCommGroup M] [Module R M]

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
  DirectLimit.lift _ _ _ _ (fun _ ↦ (of _ _ _ _ _).rTensor M)
    fun _ _ _ x ↦ by refine' x.induction_on _ _ _ <;> aesop

variable {M} in
@[simp] lemma fromDirectLimit_of_tmul {i : ι} (g : G i) (m : M) :
    fromDirectLimit f M (of _ _ _ _ i (g ⊗ₜ m)) = (of _ _ _ f i g) ⊗ₜ m :=
  lift_of (G := (G · ⊗[R] M)) _ _ (g ⊗ₜ m)

/--
the map `(limᵢ Gᵢ) ⊗ M → limᵢ (Gᵢ ⊗ M)` from the bilinear map `limᵢ Gᵢ → M → limᵢ (Gᵢ ⊗ M)` given
by the family of maps `Gᵢ → M → limᵢ (Gᵢ ⊗ M)` where `gᵢ ↦ m ↦ [gᵢ ⊗ m]`

-/
noncomputable def toDirectLimit : DirectLimit G f ⊗[R] M →ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  TensorProduct.lift <| DirectLimit.lift _ _ _ _
    (fun i ↦
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h ↦ (f _ _ h).rTensor M) i))
    fun _ _ _ g ↦ FunLike.ext _ _ (of_f (G := (G · ⊗[R] M)) (x := g ⊗ₜ ·))

variable {M} in
@[simp] lemma toDirectLimit_tmul_of
    {i : ι} (g : G i) (m : M) :
    (toDirectLimit f M <| (of _ _ G f i g) ⊗ₜ m) = (of _ _ _ _ i (g ⊗ₜ m)) := by
  rw [toDirectLimit, lift.tmul, lift_of]
  rfl

variable [IsDirected ι (· ≤ ·)]

/--
`limᵢ (Gᵢ ⊗ M)` and `(limᵢ Gᵢ) ⊗ M` are isomorphic as modules
-/
noncomputable def directLimit :
    DirectLimit (G · ⊗[R] M) (f ▷ M) ≃ₗ[R] DirectLimit G f ⊗[R] M := by
  refine LinearEquiv.ofLinear (fromDirectLimit f M) (toDirectLimit f M) ?_ ?_
    <;> cases isEmpty_or_nonempty ι
  · ext; apply Subsingleton.elim
  · exact ext (FunLike.ext _ _ fun g ↦ FunLike.ext _ _ fun _ ↦ g.induction_on <| by aesop)
  · ext; apply Subsingleton.elim
  · refine FunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ g.induction_on ?_ ?_ ?_ <;> aesop

@[simp] lemma directLimit_of_tmul {i : ι} (g : G i) (m : M) :
    directLimit f M (of _ _ _ _ _ (g ⊗ₜ m)) = (of _ _ _ f _ g) ⊗ₜ m :=
  fromDirectLimit_of_tmul f g m

@[simp] lemma directLimit_symm_tmul_of {i : ι} (g : G i) (m : M) :
    (directLimit f M).symm ((of _ _ _ _ _ g) ⊗ₜ m) = of _ _ _ (f ▷ M) _ (g ⊗ₜ m) :=
  toDirectLimit_tmul_of f g m

/--
`limᵢ (M ⊗ Gᵢ)` and `M ⊗ (limᵢ Gᵢ)` are isomorphic as modules
-/
noncomputable def directLimitRight :
    DirectLimit (M ⊗[R] G ·) (M ◁ f) ≃ₗ[R] M ⊗[R] DirectLimit G f :=
  LinearEquiv.ofLinear
    (DirectLimit.lift _ _ _ _
      (fun i ↦ of R ι _ _ i ∘ₗ (TensorProduct.comm R M (G i)).toLinearMap)
      fun i j h x ↦ x.induction_on (by aesop) (fun m g ↦
        show of R ι (G · ⊗[R] M) _ j ((f i j h).rTensor M (g ⊗ₜ m)) = _ from of_f) (by aesop))
    (DirectLimit.lift _ _ _ _
      (fun i ↦ of R ι _ _ i ∘ₗ (TensorProduct.comm R M (G i)).symm.toLinearMap)
      fun i j h x ↦ x.induction_on (by aesop) (fun m g ↦
        show of R ι (M ⊗[R] G ·) _ j ((f i j h).lTensor M (g ⊗ₜ m)) = _ from of_f) (by aesop))
    ((isEmpty_or_nonempty ι).elim (fun _ ↦ by ext; apply Subsingleton.elim)
      fun inst_ ↦ FunLike.ext _ _ fun x ↦ x.induction_on
        fun i g ↦ g.induction_on (by aesop) (fun g m ↦ by simp [lift_of]) <| by aesop)
    ((isEmpty_or_nonempty ι).elim (fun _ ↦ by ext; apply Subsingleton.elim)
      fun inst_ ↦ FunLike.ext _ _ fun x ↦ x.induction_on
        fun i g ↦ g.induction_on (by aesop) (fun g m ↦ by simp [lift_of]) <| by aesop) ≪≫ₗ
  directLimit f M ≪≫ₗ TensorProduct.comm _ _ _

@[simp] lemma directLimitRight_of_tmul {i : ι} (m : M) (g : G i) :
    directLimitRight f M (of _ _ _ _ _ (m ⊗ₜ g)) = m ⊗ₜ (of _ _ _ f _ g) := by
  simp only [directLimitRight, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply, lift_of,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul, directLimit_of_tmul]

@[simp] lemma directLimitRight_symm_tmul_of {i : ι} (m : M) (g : G i):
    (directLimitRight f M).symm (m ⊗ₜ of _ _ _ _ _ g) = of _ _ _ _ i (m ⊗ₜ g) := by
  simp only [directLimitRight, LinearEquiv.trans_symm, LinearEquiv.trans_apply, comm_symm_tmul,
    directLimit_symm_tmul_of, LinearEquiv.ofLinear_symm_apply, lift_of, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]

end TensorProduct
