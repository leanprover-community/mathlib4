/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Scheme-theoretic fiber

## Main result
- `AlgebraicGeometry.Scheme.Hom.fiber`: `f.fiber y` is the scheme theoretic fiber of `f` at `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberHomeo`: `f.fiber y` is homeomorphic to `f ⁻¹' {y}`.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage`: Finite morphisms have finite fibers.
- `AlgebraicGeometry.Scheme.Hom.discrete_fiber`: Finite morphisms have discrete fibers.

-/

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- `f.fiber y` is the scheme theoretic fiber of `f` at `y`. -/
def Scheme.Hom.fiber (f : X.Hom Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)

/-- `f.fiberι y : f.fiber y ⟶ X` is the embedding of the scheme theoretic fiber into `X`. -/
def Scheme.Hom.fiberι (f : X.Hom Y) (y : Y) : f.fiber y ⟶ X := pullback.fst _ _

instance (f : X.Hom Y) (y : Y) : (f.fiber y).CanonicallyOver X where hom := f.fiberι y

/-- The canonical map from the scheme theoretic fiber to the residue field. -/
def Scheme.Hom.fiberToSpecResidueField (f : X.Hom Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _

/-- The fiber of `f` at `y` is naturally a `κ(y)`-scheme. -/
@[reducible] def Scheme.Hom.fiberOverSpecResidueField
    (f : X.Hom Y) (y : Y) : (f.fiber y).Over (Spec (Y.residueField y)) where
  hom := f.fiberToSpecResidueField y

lemma Scheme.Hom.fiberToSpecResidueField_apply (f : X.Hom Y) (y : Y) (x : f.fiber y) :
    (f.fiberToSpecResidueField y).base x = IsLocalRing.closedPoint (Y.residueField y) :=
  Subsingleton.elim (α := PrimeSpectrum _) _ _

lemma Scheme.Hom.range_fiberι (f : X.Hom Y) (y : Y) :
    Set.range (f.fiberι y).base = f.base ⁻¹' {y} := by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

instance (f : X ⟶ Y) (y : Y) : IsPreimmersion (f.fiberι y) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- The scheme theoretic fiber of `f` at `y` is homeomorphic to `f ⁻¹' {y}`. -/
def Scheme.Hom.fiberHomeo (f : X.Hom Y) (y : Y) : f.fiber y ≃ₜ f.base ⁻¹' {y} :=
  .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]
lemma Scheme.Hom.fiberHomeo_apply (f : X.Hom Y) (y : Y) (x : f.fiber y) :
    (f.fiberHomeo y x).1 = (f.fiberι y).base x := rfl

@[simp]
lemma Scheme.Hom.fiberι_fiberHomeo_symm (f : X.Hom Y) (y : Y) (x : f.base ⁻¹' {y}) :
    (f.fiberι y).base ((f.fiberHomeo y).symm x) = x :=
  congr($((f.fiberHomeo y).apply_symm_apply x).1)

/-- A point `x` as a point in the fiber of `f` at `f x`. -/
def Scheme.Hom.asFiber (f : X.Hom Y) (x : X) : f.fiber (f.base x) :=
    (f.fiberHomeo (f.base x)).symm ⟨x, rfl⟩

@[simp]
lemma Scheme.Hom.fiberι_asFiber (f : X.Hom Y) (x : X) : (f.fiberι _).base (f.asFiber x) = x :=
  f.fiberι_fiberHomeo_symm _ _

instance (f : X ⟶ Y) [QuasiCompact f] (y : Y) : CompactSpace (f.fiber y) :=
  haveI : QuasiCompact (f.fiberToSpecResidueField y) :=
      MorphismProperty.pullback_snd _ _ inferInstance
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
    (f := f.fiberToSpecResidueField y).mp inferInstance

lemma QuasiCompact.isCompact_preimage_singleton (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    IsCompact (f.base ⁻¹' {y}) :=
  f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

instance (f : X ⟶ Y) [IsAffineHom f] (y : Y) : IsAffine (f.fiber y) :=
  haveI : IsAffineHom (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  isAffine_of_isAffineHom (f.fiberToSpecResidueField y)

instance (f : X ⟶ Y) (y : Y) [LocallyOfFiniteType f] : JacobsonSpace (f.fiber y) :=
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField y)

instance (f : X ⟶ Y) (y : Y) [IsFinite f] : Finite (f.fiber y) := by
  have H : IsFinite (f.fiberToSpecResidueField y) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsArtinianRing Γ(f.fiber y, ⊤) :=
    @IsArtinianRing.of_finite (Y.residueField y) Γ(f.fiber y, ⊤) _ _ (show _ from _) _ _
      ((HasAffineProperty.iff_of_isAffine.mp H).2.comp (.of_surjective _ (Scheme.ΓSpecIso
        (Y.residueField y)).commRingCatIsoToRingEquiv.symm.surjective))
  exact .of_injective (β := PrimeSpectrum _) _ (f.fiber y).isoSpec.hom.homeomorph.injective

lemma IsFinite.finite_preimage_singleton (f : X ⟶ Y) [IsFinite f] (y : Y) :
    (f.base ⁻¹' {y}).Finite :=
  f.range_fiberι y ▸ Set.finite_range (f.fiberι y).base

lemma Scheme.Hom.finite_preimage (f : X.Hom Y) [IsFinite f] {s : Set Y} (hs : s.Finite) :
    (f.base ⁻¹' s).Finite := by
  rw [← Set.biUnion_of_singleton s, Set.preimage_iUnion₂]
  exact hs.biUnion fun _ _ ↦ IsFinite.finite_preimage_singleton f _

instance Scheme.Hom.discrete_fiber (f : X ⟶ Y) (y : Y) [IsFinite f] :
    DiscreteTopology (f.fiber y) := inferInstance

end AlgebraicGeometry
