/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Module

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')

/-- The forward direction of `isLocalizedModule_iff_isBaseChange`. It is also used to prove the
other direction. -/
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f :=
  .of_lift_unique _ fun Q _ _ _ _ g ↦ by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s ↦ by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h ↦ ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

/-- The map `(f : M →ₗ[R] M')` is a localization of modules iff the map
`(Localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as it is the universal
bilinear map).
In particular, there is an isomorphism between `LocalizedModule S M` and `(Localization S) ⊗[R] M`
given by `m/s ↦ (1/s) ⊗ₜ m`.
-/
theorem isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange A f := by
  refine ⟨fun _ ↦ IsLocalizedModule.isBaseChange S A f, fun h ↦ ?_⟩
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, IsBaseChange.equiv_symm_apply,
    IsBaseChange.equiv_tmul, one_smul]

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

lemma Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSubmonoid T S) B] :
    Algebra.IsPushout R T A B := by
  rw [Algebra.IsPushout.comm, Algebra.isPushout_iff]
  apply IsLocalizedModule.isBaseChange S
