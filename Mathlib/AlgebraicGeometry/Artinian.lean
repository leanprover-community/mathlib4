/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology`: A scheme is Artinian
  if andonly if it is Noetherian and has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.Scheme.isArtinianRing_iff_IsArtinianScheme`: A commutative ring R is Artinian
  if and only if Spec R is Artinian.

TODO(Brian-Nugent): Show that all Artinian schemes are affine.

-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

variable (X : Scheme)

/-- A scheme `X` is locally Artinian if `𝒪ₓ(U)` is Artinian for all affine `U`. -/
class IsLocallyArtinian : Prop where
  isArtinianRing_presheaf_obj : ∀ (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

attribute [instance] IsLocallyArtinian.isArtinianRing_presheaf_obj

instance IsLocallyArtinian.isLocallyNoetherian [h : IsLocallyArtinian X] :
    IsLocallyNoetherian X where

instance IsLocallyArtinian.isArtinianRing_of_isAffine [h : IsLocallyArtinian X] [IsAffine X] :
    IsArtinianRing Γ(X, ⊤) :=
  h.1 ⟨⊤, isAffineOpen_top X⟩

lemma IsLocallyArtinian.discreteTopology_of_isAffine [IsLocallyArtinian X] [IsAffine X] :
    DiscreteTopology X := by
  have F := Scheme.isoSpec X
  apply (Homeomorph.discreteTopology_iff (AlgebraicGeometry.Scheme.Hom.homeomorph F.hom)).mpr
  exact inferInstanceAs (DiscreteTopology (PrimeSpectrum Γ(X,⊤)))

instance [h : IsLocallyArtinian X] {U : X.Opens} :
    IsLocallyArtinian U where
  isArtinianRing_presheaf_obj W :=
    have : IsArtinianRing Γ(X, U.ι ''ᵁ W) :=
      h.1 ⟨(U.ι ''ᵁ W), AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion W.2 U.ι⟩
    RingEquiv.isArtinianRing (Scheme.Hom.appIso U.ι ↑W).commRingCatIsoToRingEquiv

instance (priority := low) IsLocallyArtinian.discreteTopology [IsLocallyArtinian X] :
    DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨W, hW1, hW2, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have : IsAffine W := hW1
  have : DiscreteTopology W := IsLocallyArtinian.discreteTopology_of_isAffine W
  have : IsOpen ({⟨x, hW2⟩} : Set W) := discreteTopology_iff_forall_isOpen.mp
    (IsLocallyArtinian.discreteTopology_of_isAffine W) {⟨x, hW2⟩}
  have := this.trans W.2
  rwa [← show Subtype.val '' {⟨x, hW2⟩} = {x} from Set.image_singleton]

lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
    {X : Scheme} [IsLocallyNoetherian X] (h : topologicalKrullDim X ≤ 0) :
    IsLocallyArtinian X := by
  refine { isArtinianRing_presheaf_obj := ?_ }
  intro U
  have _ : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian U
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim, Nat.cast_zero,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  have Ft := Scheme.Hom.homeomorph (AlgebraicGeometry.IsAffineOpen.isoSpec U.2).hom
  change topologicalKrullDim (Spec Γ(X, U)) ≤ 0
  rw [← IsHomeomorph.topologicalKrullDim_eq Ft Ft.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans h

theorem IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology :
    IsLocallyArtinian X ↔ IsLocallyNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
  fun ⟨_,_⟩ ↦
    have h : topologicalKrullDim X ≤ 0 := topologicalKrullDim_zero_of_discreteTopology X
    IsLocallyArtinian.of_topologicalKrullDim_le_zero h⟩

/-- A scheme is Artinian if it is locally Artinian and quasi-compact -/
@[mk_iff]
class IsArtinianScheme : Prop extends IsLocallyArtinian X, CompactSpace X

/-- The underlying type of an Artinian Scheme is finite -/
instance IsArtinianScheme.finite [IsArtinianScheme X] :
    Finite X := finite_of_compact_of_discrete

instance IsArtinianScheme.isNoetherianScheme [IsArtinianScheme X] :
    IsNoetherian X where

/-- A scheme is Artinian if and only if it is Noetherian and has the discrete topology. -/
theorem IsArtinianScheme.iff_isNoetherian_and_discreteTopology :
    IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩,
  fun ⟨_,_⟩ =>
    {toIsLocallyArtinian := (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology X).mpr
      ⟨inferInstance, inferInstance⟩,
      toCompactSpace := inferInstance}⟩

/-- A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme -/
theorem Scheme.isArtinianRing_iff_isArtinianScheme (R : Type*) [CommRing R] :
    IsArtinianRing R ↔ IsArtinianScheme (Spec (CommRingCat.of R)) :=
  ⟨fun _ ↦ (IsArtinianScheme.iff_isNoetherian_and_discreteTopology (Spec (CommRingCat.of R))).mpr
    ⟨inferInstance, inferInstanceAs (DiscreteTopology (PrimeSpectrum R))⟩,
  fun _ => RingEquiv.isArtinianRing
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv⟩

end AlgebraicGeometry
