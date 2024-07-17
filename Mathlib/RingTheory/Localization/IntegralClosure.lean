/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/

import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizations and integral closure

We gather results about the connections between the integral closure and localization.
-/

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

open nonZeroDivisors

lemma isIntegrallyClosed_of_isLocalization [IsIntegrallyClosed R] [IsDomain R] (M : Submonoid R)
    (hM : M ≤ R⁰) [Algebra R S] [IsLocalization M S] : IsIntegrallyClosed S := by
  let K := FractionRing R
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp ‹_› hy
  refine' ⟨IsLocalization.mk' S z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr _⟩
  rw [RingHom.comp_id, hz, ← Algebra.smul_def]
  rfl
