/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Meta properties of essentially of finite type ring homomorphisms
-/

@[expose] public section

namespace RingHom.EssFiniteType

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

lemma comp {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType) :
    (g.comp f).EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp R S T

lemma comp_iff {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) :
    (g.comp f).EssFiniteType ↔ g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.comp_iff R S T

lemma of_comp (f : R →+* S) {g : S →+* T} (h : (g.comp f).EssFiniteType) :
    g.EssFiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.EssFiniteType.of_comp R S T

lemma stableUnderComposition : StableUnderComposition EssFiniteType :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg

lemma respectsIso : RespectsIso EssFiniteType :=
  stableUnderComposition.respectsIso fun e ↦ (FiniteType.of_surjective _ e.surjective).essFiniteType

lemma isStableUnderBaseChange : IsStableUnderBaseChange EssFiniteType :=
  .mk respectsIso fun R S T _ _ _ _ _ h ↦ by
    rw [essFiniteType_algebraMap] at h ⊢
    infer_instance

lemma holdsForLocalization : HoldsForLocalization EssFiniteType := by
  introv R _
  rw [essFiniteType_algebraMap]
  exact .of_isLocalization _ M

lemma residueFieldMap {f : R →+* S} [IsLocalRing R] [IsLocalRing S] [IsLocalHom f]
    (hf : f.EssFiniteType) :
    (IsLocalRing.ResidueField.map f).EssFiniteType := by
  refine .of_comp (IsLocalRing.residue R) ?_
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact .comp hf (FiniteType.of_surjective _ <| IsLocalRing.residue_surjective).essFiniteType

end RingHom.EssFiniteType
