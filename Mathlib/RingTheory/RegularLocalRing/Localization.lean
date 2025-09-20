/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.RingTheory.RegularLocalRing.AuslanderBuchsbaumSerre

/-!

# Localization of Regular Local Ring is Regular

In this file, we establish the full version of Auslander-Buchsbaum-Serre criterion and its corollary
that localization of regular local ring is regular.

-/

--set_option pp.universes true

universe u v

variable (R : Type u) [CommRing R]

theorem Auslander_Buchsbaum_Serre [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R] :
    IsRegularLocalRing R ↔ globalDimension.{v} R < ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ IsRegularLocalRing.of_globalDimension_lt_top h⟩
  rw [IsRegularLocalRing.globalDimension_eq_ringKrullDim]
  exact ringKrullDim_lt_top

lemma isRegularLocalRing_localization [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply IsRegularLocalRing.of_globalDimension_lt_top.{u, u}
  have : globalDimension.{u} (Localization.AtPrime p) ≤ globalDimension.{u} R := by
    rw [globalDimension_eq_iSup_loclization_prime R]
    apply le_iSup (fun (q : PrimeSpectrum R) ↦ globalDimension.{u} (Localization.AtPrime q.1))
      ⟨p, inferInstance⟩
  apply lt_of_le_of_lt this
  rw [IsRegularLocalRing.globalDimension_eq_ringKrullDim]
  exact ringKrullDim_lt_top

lemma IsRegularLocalRing.of_isLocalization [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] : IsRegularLocalRing S :=
  let _ := isRegularLocalRing_localization R p
  IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv
