/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.RingHom.Integral

/-!

# Integral morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is integral if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is integral.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is integral.

## TODO

- Show integral = universally closed + affine

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) extends IsAffineHom f : Prop where
  integral_app (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral

namespace IsIntegralHom

instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom := by
  show HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]

instance : IsStableUnderComposition @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition

instance : IsStableUnderBaseChange @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange

instance : ContainsIdentities @IsIntegralHom :=
  ⟨fun X ↦ ⟨fun _ _ ↦ by simpa using RingHom.isIntegral_of_surjective _ (Equiv.refl _).surjective⟩⟩

instance : IsMultiplicative @IsIntegralHom where

end IsIntegralHom

end AlgebraicGeometry
