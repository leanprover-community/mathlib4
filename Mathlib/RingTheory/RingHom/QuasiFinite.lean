/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.OpenImmersion

/-! # The meta properties of quasi-finite ring homomorphisms. -/

@[expose] public section

universe u

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring hom `R →+* S` is quasi-finite if `S` is a quasi-finite `R`-algebra. -/
@[algebraize RingHom.QuasiFinite.toAlgebra]
def QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.QuasiFinite R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
lemma QuasiFinite.toAlgebra {f : R →+* S} (hf : QuasiFinite f) :
    @Algebra.QuasiFinite R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma quasiFinite_algebraMap [Algebra R S] :
    (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S := by
  rw [RingHom.QuasiFinite, toAlgebra_algebraMap]

lemma QuasiFinite.comp {f : S →+* T} {g : R →+* S} (hf : f.QuasiFinite) (hg : g.QuasiFinite) :
    (f.comp g).QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .trans R S T

lemma QuasiFinite.of_comp {f : S →+* T} {g : R →+* S} (h : (f.comp g).QuasiFinite) :
    f.QuasiFinite := by
  algebraize [f, g, (f.comp g)]
  exact .of_restrictScalars R S T

lemma QuasiFinite.of_finite {f : S →+* T} (hf : f.Finite) : f.QuasiFinite := by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

lemma QuasiFinite.stableUnderComposition : StableUnderComposition QuasiFinite :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ comp hg hf

lemma QuasiFinite.respectsIso : RespectsIso QuasiFinite :=
  stableUnderComposition.respectsIso fun e ↦ .of_finite e.finite

lemma QuasiFinite.isStableUnderBaseChange : IsStableUnderBaseChange QuasiFinite := by
  refine .mk respectsIso ?_
  introv H
  rw [quasiFinite_algebraMap] at H ⊢
  infer_instance

lemma QuasiFinite.holdsForLocalizationAway : HoldsForLocalizationAway QuasiFinite := by
  introv R _
  exact quasiFinite_algebraMap.mpr (.of_isLocalization (.powers r))

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule
    IsScalarTower.right DivisionRing.instIsArtinianRing in
lemma QuasiFinite.ofLocalizationSpanTarget : OfLocalizationSpanTarget QuasiFinite := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  introv R hs H
  algebraize [f]
  refine ⟨fun P _ ↦ ?_⟩
  have (r : s) : Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have : Algebra.QuasiFinite R (Localization.Away r.1) := quasiFinite_algebraMap.mp (H r)
    infer_instance
  let φ (r : s) : P.Fiber S →ₐ[P.ResidueField] P.Fiber (Localization.Away r.1) :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let f : P.Fiber S →ₐ[P.ResidueField] Π r : s, (P.Fiber (Localization.Away r.1)) :=
    Pi.algHom _ _ φ
  have : IsNoetherian P.ResidueField (Π r : s, (P.Fiber (Localization.Away r.1))) :=
    isNoetherian_of_isNoetherianRing_of_finite ..
  suffices Function.Injective f from .of_injective f.toLinearMap this
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_localization _ fun J hJ ↦ ?_
  let I := (PrimeSpectrum.primesOverOrderIsoFiber R S P).symm ⟨J, inferInstance⟩
  have : ¬ (s : Set S) ⊆ I.1 := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (hs.symm.trans_le (Ideal.span_le.mpr h)))
  obtain ⟨r, hrs, hrI⟩ := Set.not_subset.mp this
  let ψ : P.Fiber (Localization.Away r) →ₐ[P.ResidueField] Localization.AtPrime J :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨IsLocalization.map (M := .powers r)
      (T := J.primeCompl) _ Algebra.TensorProduct.includeRight.toRingHom (by
      simpa [Submonoid.powers_le] using hrI), by
      simp [IsScalarTower.algebraMap_apply R S (Localization.Away r),
        -Algebra.TensorProduct.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply R _ (Localization.AtPrime J)]⟩ (fun _ _ ↦ .all _ _)
  have hψ : ψ.comp (φ ⟨r, hrs⟩) = IsScalarTower.toAlgHom _ _ _ := by ext; simp [φ, ψ]
  refine congr($hψ a).symm.trans
    (show ψ (f a ⟨r, hrs⟩) = 0 by simp only [ha, Pi.zero_apply, map_zero])

lemma QuasiFinite.propertyIsLocal : PropertyIsLocal QuasiFinite where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

open TensorProduct in
/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra,
then `T` is quasi-finite over `R` -/
lemma QuasiFinite.of_isIntegral_of_finiteType
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S} (hf : f.IsIntegral)
    {g : S →+* T} (hg : g.IsStandardOpenImmersion) (hg : (g.comp f).FiniteType) :
    (g.comp f).QuasiFinite := by
  algebraize [f, g, g.comp f]
  obtain ⟨s, hs⟩ := Algebra.IsStandardOpenImmersion.exists_away S T
  exact Algebra.QuasiFinite.of_isIntegral_of_finiteType s

end RingHom
