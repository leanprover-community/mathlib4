/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Meta properties of bijective ring homomorphisms

We show some meta properties of bijective ring homomorphisms.

## Implementation details

We don't define a `RingHom.Bijective` predicate, but use `fun f ↦ Function.Bijective f` as
the ring hom property.
-/

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom.Bijective

lemma containsIdentities : ContainsIdentities (fun f ↦ Function.Bijective f) :=
  fun _ _ ↦ Function.bijective_id

lemma stableUnderComposition : StableUnderComposition (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso (fun f ↦ Function.Bijective f) :=
  RingHom.Bijective.stableUnderComposition.respectsIso fun e ↦ e.bijective

lemma isStableUnderBaseChange : IsStableUnderBaseChange (fun f ↦ Function.Bijective f) :=
  .mk respectsIso fun R _ _ _ _ _ _ _ hf ↦
    Algebra.TensorProduct.includeLeft_bijective (S := R) hf

lemma ofLocalizationSpan : OfLocalizationSpan (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ f s hs hf ↦ bijective_of_isLocalization_of_span_eq_top (s := s) hs
    (fun r ↦ Localization.Away r.val) (fun r ↦ Localization.Away (f r.val)) f hf

end RingHom.Bijective
