/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.RingHom.Finite

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

## TODO

- Show finite morphisms are proper

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsFinite {X Y : Scheme} (f : X ⟶ Y) extends IsAffineHom f : Prop where
  finite_app (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).Finite

namespace IsFinite

instance : HasAffineProperty @IsFinite (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop)) := by
  show HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves RingHom.finite_ofLocalizationSpan]
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g ‹IsFinite f› ‹IsFinite g›

instance (priority := 900) [hf : IsFinite f] : LocallyOfFiniteType f := by
  have : targetAffineLocally (affineAnd @RingHom.FiniteType) f := by
    rw [HasAffineProperty.eq_targetAffineLocally (P := @IsFinite)] at hf
    apply targetAffineLocally_affineAnd_le RingHom.Finite.finiteType
    exact hf
  rw [targetAffineLocally_affineAnd_eq_affineLocally
    (HasRingHomProperty.isLocal_ringHomProperty @LocallyOfFiniteType)] at this
  rw [HasRingHomProperty.eq_affineLocally (P := @LocallyOfFiniteType)]
  exact this.2

end IsFinite

end AlgebraicGeometry
