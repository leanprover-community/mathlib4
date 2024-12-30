/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
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

namespace IsLocalization

include S
open TensorProduct Algebra.TensorProduct

variable (M₁ M₂ B C) [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  [Module A M₁] [Module A M₂] [IsScalarTower R A M₁] [IsScalarTower R A M₂]
  [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

theorem tensorProduct_compatibleSMul : CompatibleSMul R A M₁ M₂ where
  smul_tmul a _ _ := by
    obtain ⟨r, s, rfl⟩ := mk'_surjective S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]

/-- If `A` is a localization of `R`, tensoring two `A`-modules over `A` is the same as
tensoring them over `R`. -/
noncomputable def moduleTensorEquiv : M₁ ⊗[A] M₂ ≃ₗ[A] M₁ ⊗[R] M₂ :=
  have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A M₁ M₂

/-- If `A` is a localization of `R`, tensoring an `A`-module with `A` over `R` does nothing. -/
noncomputable def moduleLid : A ⊗[R] M₁ ≃ₗ[A] M₁ :=
  have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

/-- If `A` is a localization of `R`, tensoring two `A`-algebras over `A` is the same as
tensoring them over `R`. -/
noncomputable def algebraTensorEquiv : B ⊗[A] C ≃ₐ[A] B ⊗[R] C :=
  have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A B C

/-- If `A` is a localization of `R`, tensoring an `A`-algebra with `A` over `R` does nothing. -/
noncomputable def algebraLid : A ⊗[R] B ≃ₐ[A] B :=
  have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

@[deprecated (since := "2024-12-01")] alias tensorSelfAlgEquiv := algebraLid

set_option linter.docPrime false in
theorem bijective_linearMap_mul' : Function.Bijective (LinearMap.mul' R A) :=
  have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end IsLocalization

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

lemma Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSubmonoid T S) B] :
    Algebra.IsPushout R T A B := by
  rw [Algebra.IsPushout.comm, Algebra.isPushout_iff]
  apply IsLocalizedModule.isBaseChange S

open TensorProduct in
instance (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {α} (S : Submonoid R) {Mₛ} [AddCommGroup Mₛ] [Module R Mₛ] (f : M →ₗ[R] Mₛ)
    [IsLocalizedModule S f] : IsLocalizedModule S (Finsupp.mapRange.linearMap (α := α) f) := by
  classical
  let e : Localization S ⊗[R] M ≃ₗ[R] Mₛ :=
    (IsLocalizedModule.isBaseChange S (Localization S)
      (LocalizedModule.mkLinearMap S M)).equiv.restrictScalars R ≪≫ₗ IsLocalizedModule.iso S f
  let e' : Localization S ⊗[R] (α →₀ M) ≃ₗ[R] (α →₀ Mₛ) :=
    finsuppRight R (Localization S) M α ≪≫ₗ Finsupp.mapRange.linearEquiv e
  suffices IsLocalizedModule S (e'.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap f) by
    convert this.of_linearEquiv (e := e')
    ext
    simp
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  convert TensorProduct.isBaseChange R (α →₀ M) (Localization S) using 1
  ext a m
  apply (finsuppRight R (Localization S) M α).injective
  ext b
  apply e.injective
  suffices (if a = b then f m else 0) = e (1 ⊗ₜ[R] if a = b then m else 0) by
    simpa [e', Finsupp.single_apply, -EmbeddingLike.apply_eq_iff_eq, apply_ite e]
  split_ifs with h
  · simp [e, IsBaseChange.equiv_tmul]
  · simp only [tmul_zero, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, map_zero]
