/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.Unramified

/-!
# Étale ring homomorphisms

We show the meta properties of étale morphisms.
-/

@[expose] public section

universe u

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra. -/
@[algebraize RingHom.Etale.toAlgebra]
def Etale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Etale R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
lemma Etale.toAlgebra {f : R →+* S} (hf : Etale f) :
    @Algebra.Etale R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  rw [RingHom.Etale, toAlgebra_algebraMap]

lemma etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ ↦ ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩

lemma Etale.eq_formallyUnramified_and_smooth :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

lemma Etale.of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.Etale := by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩

lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange

lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal

lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso

lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget

lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan

lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition

end RingHom
