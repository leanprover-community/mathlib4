/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Maximal spectrum of a commutative (semi)ring

Localization results.
-/

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

variable {R}

open PrimeSpectrum Set

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its maximal ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R,
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K x)
    have hdenom : (1 : R) ∉ denom := by simpa [denom] using hrange
    rcases denom.exists_le_maximal (denom.ne_top_iff_one.mpr hdenom) with ⟨max, hmax, hle⟩
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩
    exact hd (hle ⟨n, by simp [denom, Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ <|
      (map_ne_zero_iff _ <| IsFractionRing.injective R K).mpr fun h ↦ hd (h ▸ max.zero_mem :)]⟩)
  · rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

end MaximalSpectrum

namespace PrimeSpectrum

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its prime ideals
viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R,
    Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  refine bot_unique (.trans (fun _ ↦ ?_) (MaximalSpectrum.iInf_localization_eq_bot R K).le)
  simpa only [Algebra.mem_iInf] using fun hx ⟨v, hv⟩ ↦ hx ⟨v, hv.isPrime⟩

end PrimeSpectrum

namespace MaximalSpectrum

/-- The product of localizations at all maximal ideals of a commutative semiring. -/
abbrev PiLocalization : Type _ := Π I : MaximalSpectrum R, Localization.AtPrime I.1

/-- The canonical ring homomorphism from a commutative semiring to the product of its
localizations at all maximal ideals. It is always injective. -/
def toPiLocalization : R →+* PiLocalization R := algebraMap R _

theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) := fun r r' eq ↦ by
  rw [← one_mul r, ← one_mul r']
  by_contra ne
  have ⟨I, mI, hI⟩ := (Module.eqIdeal R r r').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalization.eq_iff_exists I.primeCompl _).mp (congr_fun eq ⟨I, mI⟩)
  exact s.2 (hI hs)

theorem toPiLocalization_apply_apply {r I} : toPiLocalization R r I = algebraMap R _ r := rfl

variable {R S} (f : R →+* S) (g : S →+* P) (hf : Function.Bijective f) (hg : Function.Bijective g)

/-- Functoriality of `PiLocalization` but restricted to bijective ring homs.
If R and S are commutative rings, surjectivity would be enough. -/
noncomputable def mapPiLocalization : PiLocalization R →+* PiLocalization S :=
  Pi.ringHom fun I ↦ (Localization.localRingHom _ _ f rfl).comp <|
    Pi.evalRingHom _ (⟨_, I.2.comap_bijective f hf⟩ : MaximalSpectrum R)

theorem mapPiLocalization_naturality :
    (mapPiLocalization f hf).comp (toPiLocalization R) =
      (toPiLocalization S).comp f := by
  ext r I
  show Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

theorem mapPiLocalization_id : mapPiLocalization (.id R) Function.bijective_id = .id _ :=
  RingHom.ext fun _ ↦ funext fun _ ↦ congr($(Localization.localRingHom_id _) _)

theorem mapPiLocalization_comp :
    mapPiLocalization (g.comp f) (hg.comp hf) =
      (mapPiLocalization g hg).comp (mapPiLocalization f hf) :=
  RingHom.ext fun _ ↦ funext fun _ ↦ congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

theorem mapPiLocalization_bijective : Function.Bijective (mapPiLocalization f hf) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization f hf)
    (mapPiLocalization (f.symm : S →+* R) f.symm.bijective) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Nontrivial (R i)]

theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) := fun surj ↦ by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
  have : r = 0 := funext fun i ↦ toPiLocalization_injective _ <| funext fun I ↦ by
    replace hr := congr_fun hr ⟨_, I.2.comap_piEvalRingHom⟩
    dsimp only [toPiLocalization_apply_apply, Subtype.coe_mk] at hr
    simp_rw [toPiLocalization_apply_apply,
      ← Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply, hr]
    rw [Function.update_of_ne]; · simp_rw [Pi.zero_apply, map_zero]
    exact fun h ↦ notMem ⟨⟨i, I.1, I.2.isPrime⟩, PrimeSpectrum.ext congr($h.1)⟩
  replace hr := congr_fun hr ⟨J, max⟩
  rw [this, map_zero, Function.update_self] at hr
  exact zero_ne_one hr

variable {R}

theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose h; rw [not_finite_iff_infinite] at h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (MaximalSpectrum R) := by
  replace surj := mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩
    |>.2.comp surj
  rw [← RingHom.coe_comp, mapPiLocalization_naturality, RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end MaximalSpectrum

namespace PrimeSpectrum

/-- The product of localizations at all prime ideals of a commutative semiring. -/
abbrev PiLocalization : Type _ := Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl

/-- The canonical ring homomorphism from a commutative semiring to the product of its
localizations at all prime ideals. It is always injective. -/
def toPiLocalization : R →+* PiLocalization R := algebraMap R _

theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) :=
  fun _ _ eq ↦ MaximalSpectrum.toPiLocalization_injective R <|
    funext fun I ↦ congr_fun eq I.toPrimeSpectrum

/-- The projection from the product of localizations at primes to the product of
localizations at maximal ideals. -/
def piLocalizationToMaximal : PiLocalization R →+* MaximalSpectrum.PiLocalization R :=
  Pi.ringHom fun I ↦ Pi.evalRingHom _ I.toPrimeSpectrum

open scoped Classical in
theorem piLocalizationToMaximal_surjective : Function.Surjective (piLocalizationToMaximal R) :=
  fun r ↦ ⟨fun I ↦ if h : I.1.IsMaximal then r ⟨_, h⟩ else 0, funext fun _ ↦ dif_pos _⟩

variable {R}

/-- If R has Krull dimension ≤ 0, then `piLocalizationToIsMaximal R` is an isomorphism. -/
def piLocalizationToMaximalEquiv (h : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) :
    PiLocalization R ≃+* MaximalSpectrum.PiLocalization R where
  __ := piLocalizationToMaximal R
  invFun := Pi.ringHom fun I ↦ Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)

theorem piLocalizationToMaximal_bijective (h : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) :
    Function.Bijective (piLocalizationToMaximal R) :=
  (piLocalizationToMaximalEquiv h).bijective

theorem piLocalizationToMaximal_comp_toPiLocalization :
    (piLocalizationToMaximal R).comp (toPiLocalization R) = MaximalSpectrum.toPiLocalization R :=
  rfl

variable {S}

theorem isMaximal_of_toPiLocalization_surjective (surj : Function.Surjective (toPiLocalization R))
    (I : PrimeSpectrum R) : I.1.IsMaximal := by
  classical
  have ⟨J, max, le⟩ := I.1.exists_le_maximal I.2.ne_top
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max.isPrime⟩ 1)
  by_contra h
  have hJ : algebraMap _ _ r = _ := (congr_fun hr _).trans (Function.update_self ..)
  have hI : algebraMap _ _ r = _ := congr_fun hr I
  rw [← IsLocalization.lift_eq (M := J.primeCompl) (S := Localization J.primeCompl), hJ, map_one,
    Function.update_of_ne] at hI
  · exact one_ne_zero hI
  · intro eq; have : I.1 = J := congr_arg (·.1) eq; exact h (this ▸ max)
  · exact fun ⟨s, hs⟩ ↦ IsLocalization.map_units (M := I.1.primeCompl) _ ⟨s, fun h ↦ hs (le h)⟩

variable (f : R →+* S)

/-- A ring homomorphism induces a homomorphism between the products of localizations at primes. -/
noncomputable def mapPiLocalization : PiLocalization R →+* PiLocalization S :=
  Pi.ringHom fun I ↦ (Localization.localRingHom _ I.1 f rfl).comp (Pi.evalRingHom _ (f.specComap I))

theorem mapPiLocalization_naturality :
    (mapPiLocalization f).comp (toPiLocalization R) = (toPiLocalization S).comp f := by
  ext r I
  show Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl

theorem mapPiLocalization_id : mapPiLocalization (.id R) = .id _ := by
  ext; exact congr($(Localization.localRingHom_id _) _)

theorem mapPiLocalization_comp (g : S →+* P) :
    mapPiLocalization (g.comp f) = (mapPiLocalization g).comp (mapPiLocalization f) := by
  ext; exact congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

theorem mapPiLocalization_bijective (hf : Function.Bijective f) :
    Function.Bijective (mapPiLocalization f) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization (f : R →+* S)) (mapPiLocalization f.symm) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp, RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp, RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Nontrivial (R i)]

theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) :=
  fun surj ↦ MaximalSpectrum.toPiLocalization_not_surjective_of_infinite R <| by
    rw [← piLocalizationToMaximal_comp_toPiLocalization]
    exact (piLocalizationToMaximal_surjective _).comp surj

variable {R}

theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose h; rw [not_finite_iff_infinite] at h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (PrimeSpectrum R) := by
  replace surj := (mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩).2.comp surj
  rw [← RingHom.coe_comp, mapPiLocalization_naturality, RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end PrimeSpectrum
