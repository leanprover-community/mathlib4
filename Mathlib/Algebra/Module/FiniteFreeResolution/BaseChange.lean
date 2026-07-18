/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.FiniteFreeResolution.Basic
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flat base change of modules admitting finite free resolutions

This file proves that finite free resolutions are preserved by flat base change and localization.
-/

public section

universe v v' u u'

open TensorProduct

namespace Module

variable {R : Type u} [CommRing R] {A : Type u'} [CommRing A] [Algebra R A] [Flat R A]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] {f : M →ₗ[R] N}

theorem HasFiniteFreeResolutionOfLength.of_flat_baseChange {n : ℕ}
    (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A (A ⊗[R] M) n := by
  induction hM using induction_on with
  | zero M => exact HasFiniteFreeResolutionOfLength.zero A (A ⊗[R] M)
  | succ _ _ _ _ f g hf hg he _ ih =>
      exact ih.succ (AlgebraTensorModule.lTensor A A f) (AlgebraTensorModule.lTensor A A g)
        (Flat.lTensor_preserves_injective_linearMap f hf) (LinearMap.lTensor_surjective A hg)
          (Flat.lTensor_exact A he)

instance HasFiniteFreeResolution.of_flat_baseChange [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution A (A ⊗[R] M) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, hn.of_flat_baseChange⟩

theorem HasFiniteFreeResolutionOfLength.of_isBaseChange_of_flat [Small.{v', u'} A]
    (hf : IsBaseChange A f) {n : ℕ} (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A N n :=
  hM.of_flat_baseChange.of_linearEquiv hf.equiv

theorem HasFiniteFreeResolution.of_isBaseChange_of_flat [Small.{v', u'} A]
    (hf : IsBaseChange A f) [HasFiniteFreeResolution R M] : HasFiniteFreeResolution A N :=
  HasFiniteFreeResolution.of_linearEquiv hf.equiv

variable (S : Submonoid R)

theorem HasFiniteFreeResolutionOfLength.localizedModule
    {n : ℕ} (h : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength (Localization S) (LocalizedModule S M) n :=
  h.of_isBaseChange_of_flat
    (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M))

instance HasFiniteFreeResolution.localizedModule [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) :=
  HasFiniteFreeResolution.of_isBaseChange_of_flat
    (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M))

end Module
