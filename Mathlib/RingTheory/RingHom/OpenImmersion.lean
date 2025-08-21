/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.LocalProperties.Basic

/-! # Standard Open Immersion

We define the property `RingHom.IsStandardOpenImmersion` on ring homomorphisms: it means that the
morphism is a localization map away from some element. We also define the equivalent
`Algebra.IsStandardOpenImmersion`.
-/

universe u

namespace Algebra

open IsLocalization Away

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
  [Algebra R S] [Algebra R T]

/-- A standard open immersion is one that is a localization map away from some element. -/
@[mk_iff] class IsStandardOpenImmersion (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] : Prop where
  exists_away (R S) : ∃ r : R, IsLocalization.Away r S

open IsStandardOpenImmersion

instance (r : R) : IsStandardOpenImmersion R (Localization.Away r) :=
  ⟨r, inferInstance⟩

variable (R S T) in
@[trans] theorem IsStandardOpenImmersion.trans [Algebra S T] [IsScalarTower R S T]
    [IsStandardOpenImmersion R S] [IsStandardOpenImmersion S T] :
    IsStandardOpenImmersion R T :=
  let ⟨r, _⟩ := exists_away R S
  let ⟨s, _⟩ := exists_away S T
  have : Away (algebraMap R S (sec r s).1) T :=
    .of_associated (associated_sec_fst r s).symm
  ⟨r * (sec r s).1, mul' S T r _⟩

open _root_.TensorProduct in
instance [IsStandardOpenImmersion R T] : IsStandardOpenImmersion S (S ⊗[R] T) :=
  let ⟨r, _⟩ := exists_away R T
  ⟨algebraMap R S r, inferInstance⟩

end Algebra

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- A standard open immersion is one that is a localization map away from some element. -/
@[algebraize RingHom.IsStandardOpenImmersion.toAlgebra]
def IsStandardOpenImmersion : Prop :=
  letI := f.toAlgebra
  Algebra.IsStandardOpenImmersion R S

lemma isStandardOpenImmersion_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardOpenImmersion ↔ Algebra.IsStandardOpenImmersion R S := by
  rw [IsStandardOpenImmersion, toAlgebra_algebraMap]

namespace IsStandardOpenImmersion

protected lemma algebraMap [Algebra R S] (r : R) [IsLocalization.Away r S] :
    (algebraMap R S).IsStandardOpenImmersion :=
  isStandardOpenImmersion_algebraMap.2 ⟨r, inferInstance⟩

lemma toAlgebra {f : R →+* S} (hf : f.IsStandardOpenImmersion) :
    @Algebra.IsStandardOpenImmersion R S _ _ f.toAlgebra :=
  letI := f.toAlgebra; hf

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
  exact .trans _ S _

theorem containsIdentities : ContainsIdentities.{u} IsStandardOpenImmersion := id

theorem stableUnderComposition : StableUnderComposition.{u} IsStandardOpenImmersion := @comp

theorem respectsIso : RespectsIso.{u} IsStandardOpenImmersion :=
  stableUnderComposition.respectsIso fun e ↦ of_bijective e.bijective

theorem isStableUnderBaseChange : IsStableUnderBaseChange.{u} IsStandardOpenImmersion := by
  refine .mk respectsIso ?_
  introv h
  rw [isStandardOpenImmersion_algebraMap] at h ⊢
  infer_instance

theorem holdsForLocalizationAway : HoldsForLocalizationAway.{u} IsStandardOpenImmersion := by
  introv R h
  exact .algebraMap r

end IsStandardOpenImmersion

end RingHom
