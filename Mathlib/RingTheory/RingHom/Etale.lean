/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Etale ring homomorphisms

We show the meta properties of étale morphisms.
-/

universe u

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A ring hom `R →+* S` is etale, if `S` is an etale `R`-algebra. -/
@[algebraize RingHom.Etale.toAlgebra]
def Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Etale R _ S _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
lemma Etale.toAlgebra {f : R →+* S} (hf : Etale f) :
    @Algebra.Etale R _ S _ f.toAlgebra := hf

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

lemma etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  simp only [RingHom.Etale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  refine ⟨fun h ↦ ⟨inferInstance, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, inferInstance⟩⟩
  · constructor <;> infer_instance
  · rw [Algebra.FormallyEtale.iff_unramified_and_smooth]
    constructor <;> infer_instance

lemma Etale.eq_formallyUnramified_and_smooth :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

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
