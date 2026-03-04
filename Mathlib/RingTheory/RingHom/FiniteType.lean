/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.RingHom.Finite

/-!

# The meta properties of finite-type ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finiteType_localizationPreserves` : If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a
  finite type `R' = M⁻¹R`-algebra.
* `finiteType_ofLocalizationSpan` : `S` is a finite type `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite type `Rᵣ`-algebra.
*`RingHom.finiteType_isLocal`: `RingHom.FiniteType` is a local property.

-/

public section

namespace RingHom

open scoped Pointwise TensorProduct

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

theorem finiteType_stableUnderComposition : StableUnderComposition @FiniteType := by
  introv R hf hg
  exact hg.comp hf

theorem finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType := by
  refine finiteType_stableUnderComposition.respectsIso (fun {R S} _ _ e ↦ ?_)
  algebraize [e.toRingHom]
  apply Algebra.FiniteType.equiv (inferInstanceAs <| Algebra.FiniteType R R) <|
    .ofRingEquiv (congrFun rfl)

theorem finiteType_isStableUnderBaseChange : IsStableUnderBaseChange @FiniteType := by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    rw [finiteType_algebraMap] at h
    suffices Algebra.FiniteType S (S ⊗[R] T) by
      rw [RingHom.FiniteType]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

/-- If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a finite type `R' = M⁻¹R`-algebra. -/
theorem finiteType_localizationPreserves : RingHom.LocalizationPreserves @RingHom.FiniteType :=
  finiteType_isStableUnderBaseChange.localizationPreserves

theorem localization_away_map_finiteType (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R →+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  finiteType_localizationPreserves.away _ r _ _ hf

theorem finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FiniteType := by
  refine OfLocalizationSpan.mk _ finiteType_respectsIso (fun s hs h ↦ ?_)
  simp_rw [finiteType_algebraMap] at h ⊢
  exact Algebra.FiniteType.of_span_eq_top_source s hs h

theorem finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType := by
  introv R _
  rw [finiteType_algebraMap]
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S

theorem finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType := by
  introv R hs H
  algebraize [f]
  replace H : ∀ r ∈ s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FiniteType] at H; convert H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FiniteType.of_span_eq_top_target s hs H

theorem finiteType_isLocal : PropertyIsLocal @FiniteType :=
  ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

end RingHom
