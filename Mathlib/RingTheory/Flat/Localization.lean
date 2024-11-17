/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Flatness and localization

In this file we show that localizations are flat, and flatness is a local property (TODO).

## Main result
- `IsLocalization.flat`: a localization of a commutative ring is flat over it.
-/

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (f : M →ₗ[R] N) (hf : Function.Injective f)

namespace IsLocalization

include p hf

theorem lTensor_preserves_injective_linearMap : Function.Injective (f.lTensor S) := by
  have h := ((LinearMap.range f).isLocalizedModule S p (TensorProduct.mk R S N 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective f hf).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : f.lTensor S = Submodule.subtype _ ∘ₗ e.toLinearMap := by
    ext; show _ = (h.equiv _).1; simp [h.equiv_tmul, TensorProduct.smul_tmul']
  simpa [this] using e.injective

theorem rTensor_preserves_injective_linearMap : Function.Injective (f.rTensor S) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp (lTensor_preserves_injective_linearMap S p f hf)

omit hf

theorem flat : Module.Flat R S :=
  (Module.Flat.iff_lTensor_injective' _ _).mpr
    fun _ ↦ lTensor_preserves_injective_linearMap S p _ Subtype.val_injective

end IsLocalization

instance Localization.flat : Module.Flat R (Localization p) := IsLocalization.flat _ p
