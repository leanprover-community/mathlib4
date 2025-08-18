/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.LocalProperties.Basic

/-! # Standard Open Immersion

We define the ring hom property `RingHom.IsStandardOpenImmersion` which is one that is a
localization map away from some element. We also define the equivalent
`Algebra.IsStandardOpenImmersion`.
-/

universe u

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- A standard open immersion is one that is a localization map away from some element. -/
@[algebraize RingHom.IsStandardOpenImmersion.toAlgebra]
def IsStandardOpenImmersion : Prop :=
  letI := f.toAlgebra
  ∃ r : R, IsLocalization.Away r S

variable (R S) in
/-- A standard open immersion is one that is a localization map away from some element. -/
@[mk_iff] class _root_.Algebra.IsStandardOpenImmersion [Algebra R S] : Prop where
  exists_away : ∃ r : R, IsLocalization.Away r S

lemma _root_.Algebra.IsStandardOpenImmersion.away (r : R) :
    Algebra.IsStandardOpenImmersion R (Localization.Away r) :=
  ⟨r, inferInstance⟩

lemma isStandardOpenImmersion_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardOpenImmersion ↔ Algebra.IsStandardOpenImmersion R S := by
  rw [IsStandardOpenImmersion, Algebra.isStandardOpenImmersion_iff, toAlgebra_algebraMap]

namespace IsStandardOpenImmersion

lemma algebraMap' [Algebra R S] (r : R) [IsLocalization.Away r S] :
    (algebraMap R S).IsStandardOpenImmersion :=
  isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩

lemma toAlgebra {f : R →+* S} (hf : f.IsStandardOpenImmersion) :
    @Algebra.IsStandardOpenImmersion R S _ _ f.toAlgebra :=
  letI := f.toAlgebra; ⟨hf⟩

/-- A bijective ring map is a standard open immersion. -/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.IsStandardOpenImmersion :=
  letI := f.toAlgebra
  ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hf⟩

variable (R) in
/-- The identity map of a ring is a standard open immersion. -/
lemma id : (RingHom.id R).IsStandardOpenImmersion :=
  of_bijective Function.bijective_id

variable {f g} in
/-- The composition of two standard open immersions is a standard open immersion. -/
lemma comp (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion) :
    (g.comp f).IsStandardOpenImmersion := by
  algebraize [f, g, g.comp f]
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  let s' := (IsLocalization.Away.sec r s).1
  -- factor this out?
  have assoc : Associated (algebraMap R S s') s := by
    unfold s'
    rw [← IsLocalization.Away.sec_spec, map_pow]
    exact associated_mul_unit_left _ _ (.pow _ <| IsLocalization.Away.algebraMap_isUnit _)
  have : IsLocalization.Away (algebraMap R S s') T :=
    IsLocalization.Away.of_associated assoc.symm
  exact ⟨r * s', IsLocalization.Away.mul' S T r _⟩

theorem containsIdentities : ContainsIdentities.{u} IsStandardOpenImmersion := id

theorem stableUnderComposition : StableUnderComposition.{u} IsStandardOpenImmersion := @comp

theorem respectsIso : RespectsIso.{u} IsStandardOpenImmersion :=
  stableUnderComposition.respectsIso fun e ↦ of_bijective e.bijective

theorem isStableUnderBaseChange : IsStableUnderBaseChange.{u} IsStandardOpenImmersion := by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  obtain ⟨r, _⟩ := h
  exact ⟨algebraMap R S r, inferInstance⟩

theorem holdsForLocalizationAway : HoldsForLocalizationAway.{u} IsStandardOpenImmersion := by
  introv R h
  exact .algebraMap' r

end IsStandardOpenImmersion

end RingHom
