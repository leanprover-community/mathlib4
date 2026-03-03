/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change properties

This file proves that several constructions in linear algebra
commute with base change, as expressed by `IsBaseChange`.

* `IsBaseChange.prodMap`, `IsBaseChange.pi`: binary and finite products.

In particular, localization of modules commutes with binary and finite products.

* `IsBaseChange.directSum`: base change for direct sums

* Homomorphism modules

-/

@[expose] public section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace IsBaseChange

open TensorProduct

/-- Base change commutes with binary products. -/
lemma prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (f.prodMap g) := by
  apply of_equiv (prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
  intro p
  simp [equiv_tmul]

/-- Base change commutes with finite products. -/
lemma pi {ι : Type*} [Finite ι]
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)] [∀ i, Module S (M' i)]
    [∀ i, IsScalarTower R S (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) (hf : ∀ i, IsBaseChange S (f i)) :
    IsBaseChange S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  classical
  cases nonempty_fintype ι
  apply of_equiv <| piRight R S _ M ≪≫ₗ .piCongrRight fun i ↦ (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]

theorem finitePow (ι : Type*) [Finite ι]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {f : M →ₗ[R] M'} (hf : IsBaseChange S f) :
    IsBaseChange S (f.compLeft ι) :=
  IsBaseChange.pi (f := fun _ ↦ f) (fun _ ↦ hf)

end IsBaseChange

namespace IsLocalizedModule

variable (S : Submonoid R)

attribute [local instance] IsLocalizedModule.isScalarTower_module

/-- Localization of modules commutes with binary products. -/
instance prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  letI : Module (Localization S) M' := IsLocalizedModule.module S f
  letI : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

/-- Localization of modules commutes with finite products. -/
instance pi {ι : Type*} [Finite ι]
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  letI (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

end IsLocalizedModule

namespace IsBaseChange

section DirectSum

open TensorProduct LinearMap DirectSum

variable {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
    [∀ i, Module S (P i)] [∀ i, IsScalarTower R S (P i)]
    {ε : (i : ι) → N i →ₗ[R] P i}

/-- Base change for direct sums. -/
theorem directSum (ibc : ∀ i, IsBaseChange S (ε i)) :
    IsBaseChange S (lmap ε) := by
  classical
  apply of_equiv <| directSumRight' R S S N ≪≫ₗ congrLinearEquiv fun i ↦ (ibc i).equiv
  intros; ext
  simp [coe_directSumRight', coe_congrLinearEquiv, equiv_tmul]

variable (ι)
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
    [Module R M] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {ε : M →ₗ[R] M'}

/-- Base change for direct sums of a constant module. -/
theorem directSumPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (lmap fun _ : ι ↦ ε) :=
  directSum (fun _ : ι ↦ ibc)

theorem finsuppPow (ibc : IsBaseChange S ε) :
    IsBaseChange S (Finsupp.mapRange.linearMap (α := ι) ε) := by
  classical
  apply of_equiv <|
    LinearEquiv.baseChange R S _ _ (finsuppLEquivDirectSum ..) ≪≫ₗ
      (directSum (fun _ ↦ ibc)).equiv ≪≫ₗ (finsuppLEquivDirectSum ..).symm
  intro x
  rw [LinearEquiv.trans_apply, Finsupp.mapRange.linearMap_apply,
    LinearEquiv.symm_apply_eq]
  ext
  simp [LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, lmap_finsuppLEquivDirectSum_eq]

end DirectSum

end IsBaseChange
