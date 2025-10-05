/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change commutes with finite products

In particular, localization of modules commutes with finite products. We also
show the binary product versions.
-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace IsBaseChange

/-- Base change commutes with binary products. -/
lemma prodMap {M N M' N' : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (f.prodMap g) := by
  apply of_equiv (TensorProduct.prodRight R _ S M N ≪≫ₗ hf.equiv.prodCongr hg.equiv)
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
  apply of_equiv <| TensorProduct.piRight R S _ M ≪≫ₗ .piCongrRight fun i ↦ (hf i).equiv
  intro x
  ext i
  simp [equiv_tmul]

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
