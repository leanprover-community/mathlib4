/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Flat ring homomorphisms

In this file we define flat ring homomorphisms and show their meta properties.

-/

universe u v

open TensorProduct

/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize Module.Flat]
def RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Flat R S

lemma RingHom.flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  rw [RingHom.Flat, toAlgebra_algebraMap]

@[deprecated (since := "2025-06-03")]
alias flat_algebraMap_iff := RingHom.flat_algebraMap_iff

namespace RingHom.Flat

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/-- The identity of a ring is flat. -/
lemma id : RingHom.Flat (RingHom.id R) :=
  Module.Flat.self

/-- Composition of flat ring homomorphisms is flat. -/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

/-- Bijective ring maps are flat. -/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : Flat f := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

lemma containsIdentities : ContainsIdentities Flat := id

lemma stableUnderComposition : StableUnderComposition Flat := by
  introv R hf hg
  exact hf.comp hg

lemma respectsIso : RespectsIso Flat := by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

lemma isStableUnderBaseChange : IsStableUnderBaseChange Flat := by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance

lemma holdsForLocalizationAway : HoldsForLocalizationAway Flat := by
  introv R h
  suffices Module.Flat R S by
    rw [RingHom.Flat]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
  exact IsLocalization.flat _ (Submonoid.powers r)

lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Flat := by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r ↦ Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert h; ext
  apply Algebra.smul_def

/-- Flat is a local property of ring homomorphisms. -/
lemma propertyIsLocal : PropertyIsLocal Flat where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

lemma ofLocalizationPrime : OfLocalizationPrime Flat := by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

lemma localRingHom {f : R →+* S} (hf : f.Flat)
    (P : Ideal S) [P.IsPrime] (Q : Ideal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) :
    (Localization.localRingHom Q P f hQP).Flat := by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat, Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

open PrimeSpectrum

/-- `Spec S → Spec R` is generalizing if `R →+* S` is flat. -/
lemma generalizingMap_comap {f : R →+* S} (hf : f.Flat) : GeneralizingMap (comap f) := by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

end RingHom.Flat
