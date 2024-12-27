/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Basic

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

namespace RingHom.Flat

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/-- The identity of a ring is flat. -/
lemma id : RingHom.Flat (RingHom.id R) :=
  Module.Flat.self R

/-- Composition of flat ring homomorphisms is flat. -/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

/-- Bijective ring maps are flat. -/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : Flat f := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv R R S (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

lemma containsIdentities : ContainsIdentities Flat := id

lemma stableUnderComposition : StableUnderComposition Flat := by
  introv R hf hg
  exact hf.comp hg

lemma respectsIso : RespectsIso Flat := by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

lemma isStableUnderBaseChange : IsStableUnderBaseChange Flat := by
  apply IsStableUnderBaseChange.mk _ respectsIso
  introv h
  replace h : Module.Flat R T := by
    rw [RingHom.Flat] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
  suffices Module.Flat S (S ⊗[R] T) by
    rw [RingHom.Flat]; convert this; congr; ext; simp_rw [Algebra.smul_def]; rfl
  exact inferInstance

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

end RingHom.Flat
