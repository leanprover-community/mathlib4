/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!

# The free locus of a module

## Main definitions and results

Let `M` be a finitely presented `R`-module.
- `Module.freeLocus`: The set of points `x` in `Spec R` such that `Mₓ` is free over `Rₓ`.
- `Module.freeLocus_eq_univ_iff`:
  The free locus is the whole `Spec R` if and only if `M` is projective.
- `Module.basicOpen_subset_freeLocus_iff`: `D(f)` is contained in the free locus if and only if
  `M_f` is projective over `R_f`.
- `Module.rankAtStalk`: The function `Spec R → ℕ` sending `x` to `rank_{Rₓ} Mₓ`.
- `Module.isLocallyConstant_rankAtStalk`:
  If `M` is flat over `R`, then `rankAtStalk` is locally constant.

-/

universe uR uM

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

open PrimeSpectrum TensorProduct

/-- The free locus of a module, i.e. the set of primes `p` such that `Mₚ` is free over `Rₚ`. -/
def freeLocus : Set (PrimeSpectrum R) :=
  { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

variable {R M}

lemma mem_freeLocus {p} : p ∈ freeLocus R M ↔
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
  Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_of_isLocalization (p : PrimeSpectrum R)
    (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
    [AddCommGroup Mₚ] [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ Mₚ := by
  apply Module.Free.iff_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl r
  apply ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    algebraMap_end_apply, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
    IsLocalization.map_id_mk']
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
    IsLocalization.map_id_mk']

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_iff_tensor (p : PrimeSpectrum R)
    (Rₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ (Rₚ ⊗[R] M) := by
  have := (isLocalizedModule_iff_isBaseChange p.asIdeal.primeCompl _ _).mpr
    (TensorProduct.isBaseChange R M Rₚ)
  exact mem_freeLocus_of_isLocalization p Rₚ (f := TensorProduct.mk R Rₚ M 1)

lemma freeLocus_congr {M'} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    freeLocus R M = freeLocus R M' := by
  ext p
  exact mem_freeLocus_of_isLocalization _ _ _
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M' ∘ₗ e.toLinearMap)

open TensorProduct in
lemma comap_freeLocus_le {A} [CommRing A] [Algebra R A] :
    comap (algebraMap R A) ⁻¹' freeLocus R M ≤ freeLocus A (A ⊗[R] M) := by
  intro p hp
  let Rₚ := Localization.AtPrime (comap (algebraMap R A) p).asIdeal
  let Aₚ := Localization.AtPrime p.asIdeal
  rw [Set.mem_preimage, mem_freeLocus_iff_tensor _ Rₚ] at hp
  rw [mem_freeLocus_iff_tensor _ Aₚ]
  letI algebra : Algebra Rₚ Aₚ := (Localization.localRingHom
    (comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) rfl).toAlgebra
  have : IsScalarTower R Rₚ Aₚ := IsScalarTower.of_algebraMap_eq'
    (by simp [Rₚ, Aₚ, algebra, RingHom.algebraMap_toAlgebra, Localization.localRingHom,
        ← IsScalarTower.algebraMap_eq])
  let e := AlgebraTensorModule.cancelBaseChange R Rₚ Aₚ Aₚ M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A Aₚ Aₚ M).symm
  exact .of_equiv e

lemma freeLocus_localization (S : Submonoid R) :
    freeLocus (Localization S) (LocalizedModule S M) =
      comap (algebraMap R _) ⁻¹' freeLocus R M := by
  ext p
  simp only [Set.mem_preimage]
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : S ≤ p'.primeCompl := fun x hx H ↦
    p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H (IsLocalization.map_units _ ⟨x, hx⟩))
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeCompl M
  letI : Algebra (Localization S) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S p'.primeCompl hp'
  have : IsScalarTower R (Localization S) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime Rₚ p.asIdeal := by
    have := IsLocalization.isLocalization_of_submonoid_le (Localization S) Rₚ _ _ hp'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization S)) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  letI : Module (Localization S) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization S) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [p', Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization S) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization S
    (Localization S)
  have : IsLocalizedModule p.asIdeal.primeCompl l := by
    have : IsLocalizedModule p'.primeCompl (l.restrictScalars R) :=
      inferInstanceAs (IsLocalizedModule p'.primeCompl
        (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p'.primeCompl M)))
    have : IsLocalizedModule (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p'.primeCompl ..
    apply IsLocalizedModule.of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization S) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective S x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  rw [mem_freeLocus_of_isLocalization (R := Localization S) p Rₚ Mₚ l]
  rfl

lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M] :
    freeLocus R M = Set.univ ↔ Module.Projective R M := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H ↦ Module.projective_of_localization_maximal fun I hI ↦
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x ↦ Module.free_of_flat_of_isLocalRing⟩

lemma freeLocus_eq_univ [Module.FinitePresentation R M] [Module.Flat R M] :
    freeLocus R M = Set.univ := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact fun x ↦ Module.free_of_flat_of_isLocalRing

lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ freeLocus R M ↔
      Module.Projective (Localization.Away f) (LocalizedModule (.powers f) M) := by
  rw [← freeLocus_eq_univ_iff, freeLocus_localization,
    Set.preimage_eq_univ_iff, localization_away_comap_range _ f]

lemma isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (freeLocus R M) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨basicOpen r, basicOpen_subset_freeLocus_iff.mpr inferInstance, (basicOpen r).2, hr⟩

variable (M) in
/-- The rank of `M` at the stalk of `p` is the rank of `Mₚ` as a `Rₚ`-module. -/
noncomputable
def rankAtStalk (p : PrimeSpectrum R) : ℕ :=
  Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] :
    IsLocallyConstant (fun x : freeLocus R M ↦ rankAtStalk M x.1) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  refine ⟨Subtype.val ⁻¹' basicOpen f, (basicOpen f).2.preimage continuous_subtype_val, hf, ?_⟩
  rintro ⟨p, hp''⟩ hp
  let p' := Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
  have hp' : Submonoid.powers f ≤ p.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  letI : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  letI : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Rₚ, Mₚ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • r' • m by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
  have : IsLocalizedModule p.asIdeal.primeCompl (l.restrictScalars R) :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
    ((IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))))
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l :=
      IsLocalizedModule.of_restrictScalars p.asIdeal.primeCompl ..
  have := Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
  simp [Rₚ, rankAtStalk, this, hf'']

lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Flat R M] :
    IsLocallyConstant (rankAtStalk (R := R) M) := by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr freeLocus_eq_univ).trans (Homeomorph.Set.univ (PrimeSpectrum R))
  convert isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

end Module
