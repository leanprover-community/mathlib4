/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Algebra.Category.Ring.Epi

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

Also see `AlgebraicGeometry.IsFinite.finite_preimage_singleton` in
`Mathlib/AlgebraicGeometry/Fiber.lean` for the fact that finite morphisms have finite fibers.

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  finite_app (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite

namespace IsFinite

instance : HasAffineProperty @IsFinite
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom) := by
  show HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

instance : IsStableUnderComposition @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

instance : IsStableUnderBaseChange @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

instance : ContainsIdentities @IsFinite :=
  HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities

instance : IsMultiplicative @IsFinite where

lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsFinite (Spec.map f) ↔ f.hom.Finite := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_iff_right (by infer_instance),
    RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g ‹IsFinite f› ‹IsFinite g›

lemma iff_isIntegralHom_and_locallyOfFiniteType :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom),
    RingHom.finite_iff_isIntegral_and_finiteType, ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).symm

lemma eq_inf :
    @IsFinite = (@IsIntegralHom ⊓ @LocallyOfFiniteType : MorphismProperty Scheme) := by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _

instance (priority := 900) [IsFinite f] : IsIntegralHom f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).1

instance (priority := 900) [hf : IsFinite f] : LocallyOfFiniteType f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).2

lemma _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  wlog hY : IsAffine Y
  · show _ ↔ _ ∧ monomorphisms _ f
    rw [IsLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
    simp_rw [this, forall_and, monomorphisms]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion),
    HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    RingHom.surjective_iff_epi_and_finite, @and_comm (Epi _), ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    Iff.trans ?_ (arrow_mk_iso_iff (monomorphisms _) (arrowIsoSpecΓOfIsAffine f).symm)
  trans Mono (f.app ⊤).op
  · exact ⟨fun h ↦ inferInstance, fun h ↦ show Epi (f.app ⊤).op.unop by infer_instance⟩
  exact (Functor.mono_map_iff_mono Scheme.Spec _).symm

lemma _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono :
    @IsClosedImmersion = (@IsFinite ⊓ monomorphisms Scheme : MorphismProperty _) := by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] : IsFinite f :=
  ((IsClosedImmersion.iff_isFinite_and_mono f).mp ‹_›).1

end IsFinite

/-- If `X` is a jacobson scheme and `k` is a field,
`Spec(k) ⟶ X` is finite iff it is (locally) of finite type.
(The statement is more general to allow the empty scheme as well) -/
lemma isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Subsingleton X] [IsReduced X] [JacobsonSpace Y] :
    IsFinite f ↔ LocallyOfFiniteType f := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullbackCover f).map i).isOpenEmbedding.injective.subsingleton
    have inst (i) := isReduced_of_isOpenImmersion ((Y.affineCover.pullbackCover f).map i)
    have inst (i) := JacobsonSpace.of_isOpenEmbedding (Y.affineCover.map i).isOpenEmbedding
    exact forall_congr' fun i ↦ this ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ R, X = Spec R generalizing X
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) X.isoSpec.inv,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) X.isoSpec.inv]
    have inst := X.isoSpec.inv.isOpenEmbedding.injective.subsingleton
    refine this ⟨_, rfl⟩
  cases isEmpty_or_nonempty X
  · exact ⟨inferInstance, inferInstance⟩
  have : IrreducibleSpace X := ⟨‹_›⟩
  obtain ⟨R, rfl⟩ := hX
  have : IsDomain R := (affine_isIntegral_iff R).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [IsFinite.SpecMap_iff, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := (PrimeSpectrum.t1Space_iff_isField (R := R)).mp (show T1Space (Spec R) by infer_instance)
  letI := this.toField
  letI := φ.hom.toAlgebra
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  show Module.Finite _ _ ↔ Algebra.FiniteType _ _
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ finite_of_finite_type_of_isJacobsonRing _ _⟩

@[stacks 01TB "(1) => (3)"]
lemma Scheme.Hom.closePoints_subset_preimage_closedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [JacobsonSpace Y] [LocallyOfFiniteType f] :
    closedPoints X ⊆ f.base ⁻¹' closedPoints Y := by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClosedMap.isClosed_range

@[stacks 01TB "(1) => (2)"]
lemma isClosed_singleton_iff_locallyOfFiniteType {X : Scheme.{u}} [JacobsonSpace X] {x : X} :
    IsClosed ({x} : Set X) ↔ LocallyOfFiniteType (X.fromSpecResidueField x) := by
  constructor
  · exact fun H ↦ have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

end AlgebraicGeometry
