/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and Locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian_iff_IsLocallyNoetherian_and_DiscreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme_iff_IsNoetherian_and_Finite`: A scheme is Artinian if and
  only if it is Noetherian and has the discrete topology.

* `IsLocallyArtinian_Opens_IsLocallyArtinian`: An open subset of a Locally Artinian scheme is
  locally Artinian (when considered as a scheme in the natural way)

* `inst_IsArtinianScheme_Finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.IsArtinianRing_iff_IsArtinianScheme`: A commutative ring R is Artinian if
  and only if Spec R is Artinian.

TODO: Show that all Artinian schemes are affine.

-/

noncomputable section

namespace AlgebraicGeometry

variable (X : Scheme)

/-- A scheme `X` is locally Artinian if `𝒪ₓ(U)` is Artinian for all affine `U`. -/
class IsLocallyArtinian : Prop where
  component_artinian : ∀ (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

lemma IsLocallyArtinian_IsLocallyNoetherian :
    IsLocallyArtinian X → IsLocallyNoetherian X := fun hA =>
  {component_noetherian := fun U =>
    by
      have _ := hA.1 U
      infer_instance}

lemma IsArtinianRing_DiscreteTopology (R : Type*) [CommRing R] [IsArtinianRing R] :
    DiscreteTopology (PrimeSpectrum R) := by
  apply DiscreteTopology.of_finite_of_isClosed_singleton
  intro p
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr
  exact Ideal.isMaximal_of_isPrime p.asIdeal

instance IsLocallyArtinian_IsAffine_IsArtinianRing [h : IsLocallyArtinian X] [IsAffine X] :
    IsArtinianRing Γ(X, ⊤) :=
  h.1 ⟨⊤, isAffineOpen_top X⟩

lemma IsLocallyArtinian_IsAffine_DiscreteTopology [IsLocallyArtinian X] [IsAffine X] :
    DiscreteTopology X := by
  have F := AlgebraicGeometry.Scheme.isoSpec X
  apply (Homeomorph.discreteTopology_iff (AlgebraicGeometry.Scheme.Hom.homeomorph F.hom)).mpr
  exact IsArtinianRing_DiscreteTopology Γ(X,⊤)

instance IsLocallyArtinian_Opens_IsLocallyArtinian [h : IsLocallyArtinian X] {U : X.Opens} :
    IsLocallyArtinian U := by
  refine { component_artinian := ?_ }
  intro W
  have F := (Scheme.Hom.appIso U.ι ↑W).commRingCatIsoToRingEquiv
  have _ : IsArtinianRing Γ(X, U.ι ''ᵁ W) :=
    h.1 ⟨(U.ι ''ᵁ W), AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion W.2 U.ι⟩
  exact RingEquiv.isArtinianRing F

lemma IsLocallyArtinian_DiscreteTopology :
    IsLocallyArtinian X → DiscreteTopology X := by
  intro hA
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have : x ∈ (⊤ : X.Opens) := trivial
  obtain ⟨W, hW1, hW2, _⟩ := exists_isAffineOpen_mem_and_subset this
  have _ : IsAffine W := hW1
  have : DiscreteTopology W := IsLocallyArtinian_IsAffine_DiscreteTopology W
  have : IsOpen ({(⟨x, hW2⟩)} : Set W) := by
    apply discreteTopology_iff_forall_isOpen.mp
    exact IsLocallyArtinian_IsAffine_DiscreteTopology W
  have _ := IsOpen.trans this W.2
  have : Subtype.val '' {⟨x, hW2⟩} = {x} := Set.image_singleton
  rw[← this]
  assumption

instance inst_IsLocallyArtinian_DiscreteTopology [h : IsLocallyArtinian X] :
    DiscreteTopology X :=
  IsLocallyArtinian_DiscreteTopology X h

theorem IsNoetherianRing_DiscreteTopololgy_IsArtinianRing
(R : Type*) [CommRing R] [IsNoetherianRing R] [DiscreteTopology (PrimeSpectrum R)] :
    IsArtinianRing R := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  apply Ring.krullDimLE_zero_iff.mpr
  intro I hI
  let p : PrimeSpectrum R := ⟨I, hI⟩
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp
  exact isClosed_singleton

lemma IsLocallyNoetherian_DiscreteTopology_IsLocallyArtinian
[IsLocallyNoetherian X] [DiscreteTopology X] :
    IsLocallyArtinian X := by
  refine { component_artinian := ?_ }
  intro U
  have _ : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian U
  have _ : DiscreteTopology (PrimeSpectrum Γ(X,U)) := by
    change DiscreteTopology (Spec Γ(X,U))
    have F := AlgebraicGeometry.IsAffineOpen.isoSpec U.2
    apply (Homeomorph.discreteTopology_iff (AlgebraicGeometry.Scheme.Hom.homeomorph F.hom)).mp
    exact instDiscreteTopologySubtype
  exact IsNoetherianRing_DiscreteTopololgy_IsArtinianRing Γ(X, U)

theorem IsLocallyArtinian_iff_IsLocallyNoetherian_and_DiscreteTopology :
    IsLocallyArtinian X ↔ IsLocallyNoetherian X ∧ DiscreteTopology X :=
  ⟨fun h => ⟨IsLocallyArtinian_IsLocallyNoetherian X h, IsLocallyArtinian_DiscreteTopology X h⟩,
  fun ⟨_,_⟩ => IsLocallyNoetherian_DiscreteTopology_IsLocallyArtinian X⟩

instance inst_IsLocallyArtinian_IsLocallyNoetherian [IsLocallyArtinian X] :
    IsLocallyNoetherian X := IsLocallyArtinian_IsLocallyNoetherian X inferInstance

@[mk_iff]
class IsArtinianScheme : Prop extends IsLocallyArtinian X, CompactSpace X

instance inst_IsArtinianScheme_Finite [h : IsArtinianScheme X] :
    Finite X := @finite_of_compact_of_discrete X _ _ _

instance inst_IsArtinianScheme_IsNoetherianScheme [IsArtinianScheme X] :
    IsNoetherian X :=
      { toIsLocallyNoetherian := inferInstance,
        toCompactSpace := inferInstance}

theorem IsArtinianScheme_iff_IsNoetherian_and_DiscreteTopology :
    IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩,
  fun ⟨_,_⟩ =>
    {toIsLocallyArtinian := IsLocallyNoetherian_DiscreteTopology_IsLocallyArtinian X,
      toCompactSpace := inferInstance}⟩

/-- A commutative ring R is Artinian if and only if Spec R is and Artinian scheme -/
theorem IsArtinianRing_iff_IsArtinianScheme (R : Type*) [CommRing R] :
    IsArtinianRing R ↔ IsArtinianScheme (Spec (CommRingCat.of R)) := by
  constructor
  · intro _
    apply (IsArtinianScheme_iff_IsNoetherian_and_DiscreteTopology (Spec (CommRingCat.of R))).mpr
    exact ⟨inferInstance, IsArtinianRing_DiscreteTopology R⟩
  intro _
  have F := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  exact RingEquiv.isArtinianRing F

end AlgebraicGeometry
