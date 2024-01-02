/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Module

/-!
# Localized Module

Given a commutative ring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/

variable {R : Type*} [CommRing R] (S : Submonoid R)
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')

/-- The forward direction of `isLocalizedModule_iff_isBaseChange`. It is also used to prove the
other direction. -/
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f := by
  refine IsBaseChange.of_lift_unique _ (fun Q _ _ _ _ g ↦ ?_)
  have := IsLocalizedModule.is_universal S f g <| by
    intro s
    simp_rw [Module.End_isUnit_iff, Function.bijective_iff_existsUnique,
      Module.algebraMap_end_apply]
    intro q
    refine ⟨(IsLocalization.mk' _ 1 s : A) • q, ?_, ?_⟩
    · simp only [← smul_assoc, IsLocalization.smul_mk'_self, map_one, one_smul]
    · rintro q rfl
      simp only [smul_comm _ (s : R), ← smul_assoc, IsLocalization.smul_mk'_self, map_one,
        one_smul]
  rcases this with ⟨ℓ, rfl, h₂⟩
  refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h ↦ ?_⟩
  ext x
  simp [← h₂ (LinearMap.restrictScalars R g'') h]

/-- The map `(f : M →ₗ[R] M')` is a localization of modules iff the map
`(localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as it is the universal
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
