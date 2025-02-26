/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Localization of modules commutes with finite products
-/

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

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
