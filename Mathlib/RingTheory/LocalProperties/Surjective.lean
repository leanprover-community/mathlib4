/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# `Surjective` is a local property

In this file, we prove that `Surjective` is a local property.


## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `localizationPreserves_surjective` :  `M⁻¹R →+* M⁻¹S` is surjective if `R →+* S` is surjective.
* `surjective_ofLocalizationSpan` : `R →+* S` is surjective if there exists a set `{ r }` that
  spans `R` such that `Rᵣ →+* Sᵣ` is surjective.
* `surjective_localRingHom_of_surjective` : A surjective ring homomorphism `R →+* S` induces a
  surjective homomorphism `R_{f⁻¹(P)} →+* S_P` for every prime ideal `P` of `S`.

-/

universe u

/-- `M⁻¹R →+* M⁻¹S` is surjective if `R →+* S` is surjective. -/
theorem localizationPreserves_surjective :
    RingHom.LocalizationPreserves fun {R S} _ _ f => Function.Surjective f := by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']

/-- `R →+* S` is surjective if there exists a set `{ r }` that spans `R` such that
  `Rᵣ →+* Sᵣ` is surjective. -/
theorem surjective_ofLocalizationSpan :
    RingHom.OfLocalizationSpan fun {R S} _ _ f => Function.Surjective f := by
  introv R e H
  rw [← Set.range_iff_surjective, Set.eq_univ_iff_forall]
  letI := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r : R)) a
  erw [IsLocalization.map_mk'] at e'
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, Subtype.coe_mk, ← map_mul] at e'
  obtain ⟨⟨_, n', rfl⟩, e''⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f r)) _).mp e'
  dsimp only at e''
  rw [mul_comm x, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, ← pow_add] at e''
  exact ⟨n' + n, _, e''.symm⟩

/-- A surjective ring homomorphism `R →+* S` induces a surjective homomorphism `R_{f⁻¹(P)} →+* S_P`
for every prime ideal `P` of `S`. -/
theorem surjective_localRingHom_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Function.Surjective f) (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  localizationPreserves_surjective _ _ _ _ h

lemma surjective_respectsIso : RingHom.RespectsIso (fun f ↦ Function.Surjective f) := by
  apply RingHom.StableUnderComposition.respectsIso
  · intro R S T _ _ _ f g hf hg
    simp only [RingHom.coe_comp]
    exact Function.Surjective.comp hg hf
  · intro R S _ _ e
    exact EquivLike.surjective e
