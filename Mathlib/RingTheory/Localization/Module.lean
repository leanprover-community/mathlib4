/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

#align_import ring_theory.localization.module from "leanprover-community/mathlib"@"2e59a6de168f95d16b16d217b808a36290398c0a"

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `LinearIndependent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `Basis.ofIsLocalizedModule` / `Basis.localizationLocalization`: promote an `R`-basis `b` of `A`
   to an `Rₛ`-basis of `Aₛ`, where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s`
   respectively
 * `LinearIndependent.iff_fractionRing`: `b` is linear independent over `R` iff it is
   linear independent over `Frac(R)`
-/


open nonZeroDivisors

section Localization

variable {R : Type*} (Rₛ : Type*) [CommSemiring R] (S : Submonoid R)

section IsLocalizedModule

section AddCommMonoid

open Submodule

variable [CommSemiring Rₛ] [Algebra R Rₛ] [hT : IsLocalization S Rₛ]
variable {M M' : Type*} [AddCommMonoid M] [Module R M] [Module Rₛ M] [IsScalarTower R Rₛ M]
  [AddCommMonoid M'] [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M'] (f : M →ₗ[R] M')
  [IsLocalizedModule S f]

theorem span_eq_top_of_isLocalizedModule {v : Set M} (hv : span R v = ⊤) :
    span Rₛ (f '' v) = ⊤ := top_unique fun x _ ↦ by
  obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj S f x
  rw [Submonoid.smul_def, ← algebraMap_smul Rₛ, ← Units.smul_isUnit (IsLocalization.map_units Rₛ s),
    eq_comm, ← inv_smul_eq_iff] at h
  refine h ▸ smul_mem _ _  (span_subset_span R Rₛ _ ?_)
  rw [← LinearMap.coe_restrictScalars R, ← LinearMap.map_span, hv]
  exact mem_map_of_mem mem_top

theorem LinearIndependent.of_isLocalizedModule {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (f ∘ v) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro t g hg i hi
  choose! a g' hg' using IsLocalization.exist_integer_multiples S t g
  have h0 : f (∑ i ∈ t, g' i • v i) = 0 := by
    apply_fun ((a : R) • ·) at hg
    rw [smul_zero, Finset.smul_sum] at hg
    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← smul_assoc, ← hg' i hi, map_smul, Function.comp_apply, algebraMap_smul]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S f).mp h0
  simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at hs
  specialize hv t _ hs i hi
  rw [← (IsLocalization.map_units Rₛ a).mul_right_eq_zero, ← Algebra.smul_def, ← hg' i hi]
  exact (IsLocalization.map_eq_zero_iff S _ _).2 ⟨s, hv⟩

theorem LinearIndependent.localization {ι : Type*} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  have := isLocalizedModule_id S M Rₛ
  exact hli.of_isLocalizedModule Rₛ S .id
#align linear_independent.localization LinearIndependent.localization

end AddCommMonoid

section Basis

variable [CommRing Rₛ] [Algebra R Rₛ] [hT : IsLocalization S Rₛ]

open Submodule

variable {M Mₛ : Type*} [AddCommGroup M] [AddCommGroup Mₛ] [Module R M] [Module R Mₛ] [Module R Mₛ]
  [Module Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] [IsScalarTower R Rₛ Mₛ]
  {ι : Type*} (b : Basis ι R M)

/-- If `M` has an `R`-basis, then localizing `M` at `S` has a basis over `R` localized at `S`. -/
noncomputable def Basis.ofIsLocalizedModule : Basis ι Rₛ Mₛ :=
  .mk (b.linearIndependent.of_isLocalizedModule Rₛ S f) <| by
    rw [Set.range_comp, span_eq_top_of_isLocalizedModule Rₛ S _ b.span_eq]

@[simp]
theorem Basis.ofIsLocalizedModule_apply (i : ι) : b.ofIsLocalizedModule Rₛ S f i = f (b i) := by
  rw [ofIsLocalizedModule, coe_mk, Function.comp_apply]

@[simp]
theorem Basis.ofIsLocalizedModule_repr_apply (m : M) (i : ι) :
    ((b.ofIsLocalizedModule Rₛ S f).repr (f m)) i = algebraMap R Rₛ (b.repr m i) := by
  suffices ((b.ofIsLocalizedModule Rₛ S f).repr.toLinearMap.restrictScalars R) ∘ₗ f =
      Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext b fun i ↦ ?_
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, ← b.ofIsLocalizedModule_apply Rₛ S f, repr_self, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, repr_self, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

theorem Basis.ofIsLocalizedModule_span :
    span R (Set.range (b.ofIsLocalizedModule Rₛ S f)) = LinearMap.range f := by
  calc span R (Set.range (b.ofIsLocalizedModule Rₛ S f))
    _ = span R (f '' (Set.range b)) := by congr; ext; simp
    _ = map f (span R (Set.range b)) := by rw [Submodule.map_span]
    _ = LinearMap.range f := by rw [b.span_eq, Submodule.map_top]

end Basis

end IsLocalizedModule

section LocalizationLocalization

variable {R : Type*} (Rₛ : Type*) [CommSemiring R] [CommRing Rₛ] [Algebra R Rₛ]
variable (S : Submonoid R) [hT : IsLocalization S Rₛ]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ]
variable [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]
variable [hA : IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]

open Submodule

theorem LinearIndependent.localization_localization {ι : Type*} {v : ι → A}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ ((algebraMap A Aₛ) ∘ v) :=
  hv.of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap
#align linear_independent.localization_localization LinearIndependent.localization_localization

theorem span_eq_top_localization_localization {v : Set A} (hv : span R v = ⊤) :
    span Rₛ (algebraMap A Aₛ '' v) = ⊤ :=
  span_eq_top_of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap hv
#align span_eq_top.localization_localization span_eq_top_localization_localization

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[Algebra A Aₛ]` is `localizationAlgebra`.
-/
noncomputable def Basis.localizationLocalization {ι : Type*} (b : Basis ι R A) : Basis ι Rₛ Aₛ :=
  b.ofIsLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap
#align basis.localization_localization Basis.localizationLocalization

@[simp]
theorem Basis.localizationLocalization_apply {ι : Type*} (b : Basis ι R A) (i) :
    b.localizationLocalization Rₛ S Aₛ i = algebraMap A Aₛ (b i) :=
  b.ofIsLocalizedModule_apply Rₛ S _ i
#align basis.localization_localization_apply Basis.localizationLocalization_apply

@[simp]
theorem Basis.localizationLocalization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) :
    (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
      algebraMap R Rₛ (b.repr x i) := b.ofIsLocalizedModule_repr_apply Rₛ S _ _ i
#align basis.localization_localization_repr_algebra_map Basis.localizationLocalization_repr_algebraMap

theorem Basis.localizationLocalization_span {ι : Type*} (b : Basis ι R A) :
    Submodule.span R (Set.range (b.localizationLocalization Rₛ S Aₛ)) =
      LinearMap.range (IsScalarTower.toAlgHom R A Aₛ) := b.ofIsLocalizedModule_span Rₛ S _

end LocalizationLocalization


section FractionRing

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem LinearIndependent.iff_fractionRing {ι : Type*} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨LinearIndependent.localization K R⁰,
    LinearIndependent.restrict_scalars (smul_left_injective R one_ne_zero)⟩
#align linear_independent.iff_fraction_ring LinearIndependent.iff_fractionRing

end FractionRing

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
variable {M N : Type*}
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

open IsLocalization

/-- An `R`-linear map between two `S⁻¹R`-modules is actually `S⁻¹R`-linear. -/
def LinearMap.extendScalarsOfIsLocalization (f : M →ₗ[R] N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro r m
    simp only [RingHom.id_apply]
    rcases mk'_surjective S r with ⟨r, s, rfl⟩
    calc f (mk' A r s • m)
        = ((s : R) • mk' A 1 s) • f (mk' A r s • m) := by simp
      _ = (mk' A 1 s) • (s : R) • f (mk' A r s • m) := by rw [smul_comm, smul_assoc]
      _ = (mk' A 1 s) • f ((s : R) • mk' A r s • m) := by simp
      _ = (mk' A 1 s) • f (r • m) := by rw [← smul_assoc, smul_mk'_self, algebraMap_smul]
      _ = (mk' A 1 s) • r • f m := by simp
      _ = mk' A r s • f m := by rw [smul_comm, ← smul_assoc, smul_mk'_one]

@[simp] lemma LinearMap.restrictScalars_extendScalarsOfIsLocalization (f : M →ₗ[R] N) :
    (f.extendScalarsOfIsLocalization S A).restrictScalars R = f := rfl

@[simp] lemma LinearMap.extendScalarsOfIsLocalization_apply (f : M →ₗ[A] N) :
    f.extendScalarsOfIsLocalization S A = f := rfl

end
