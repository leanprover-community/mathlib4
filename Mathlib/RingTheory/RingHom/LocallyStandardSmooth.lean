/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth is locally standard smooth

In this file we show that a ring homomorphism is smooth if and only if it is locally standard
smooth.
-/

universe u

@[expose] public section

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}

/-- Any standard smooth ring homomorphism is smooth. -/
lemma IsStandardSmooth.smooth {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : IsStandardSmooth f) : Smooth f := by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

/-- Any smooth ring homomorphism is locally standard smooth. -/
theorem Smooth.locally_isStandardSmooth (hf : f.Smooth) : Locally IsStandardSmooth f := by
  algebraize [f]
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  refine ⟨s, hs, fun t ht ↦ ?_⟩
  dsimp only
  rw [← f.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_eq, isStandardSmooth_algebraMap]
  exact h t ht

/-- A ring homomorphism is smooth if and only if it is locally standard smooth. -/
theorem smooth_iff_locally_isStandardSmooth : Smooth f ↔ Locally IsStandardSmooth f := by
  refine ⟨fun hf ↦ hf.locally_isStandardSmooth, fun hf ↦ ?_⟩
  rw [← locally_iff_of_localizationSpanTarget Smooth.propertyIsLocal.respectsIso
    Smooth.ofLocalizationSpanTarget]
  exact locally_of_locally (fun hf ↦ hf.smooth) hf

end RingHom
