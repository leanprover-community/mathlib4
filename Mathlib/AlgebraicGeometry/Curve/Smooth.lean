/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth morphisms of schemes

In this file, we define when a morphism of schemes is smooth.
-/

/--
Smooth homomorphisms between rings.
-/
def RingHom.IsSmooth {R A : Type _} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  @Algebra.Smooth R _ A _ (RingHom.toAlgebra f)

namespace AlgebraicGeometry

section ClosedImmersion

/--
Closed immersions between locally ringed spaces.
-/
class LocallyRingedSpace.IsClosedImmersion {X : LocallyRingedSpace} {Y : LocallyRingedSpace}
    (f : X ⟶ Y) : Prop where
  val_base_closed : ClosedEmbedding f.val.base
  epi : ∀ (x : Y.toPresheafedSpace),
    Function.Surjective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.val.c)

/--
Closed immersions between locally ringed spaces.
-/
abbrev IsClosedImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsClosedImmersion f

end ClosedImmersion

section Smooth

/--
Given a scheme morphism `f : X ⟶ Y` and a point `x : X.toTopCat`, stating that `f` is smooth at
`X`.
-/
class Scheme.IsSmoothAt {X Y : Scheme} (f : X ⟶ Y) (x : X.toTopCat) : Type _ where
/- A ring whose prime spectrum is isomorphic to some open nbd of `x`. --/
  R : CommRingCat
/- A ring whose prime spectrum is isomorphic to some open subset of `Y` --/
  S : CommRingCat
/- An open nbd of x. --/
  U : TopologicalSpace.OpenNhds x
/- An open subset of `Y`. --/
  V : TopologicalSpace.Opens Y.toTopCat
/- `f` maps `U` into `V`. --/
  le_preimage : U.obj ≤ TopologicalSpace.Opens.mk (f.val.base ⁻¹' V.carrier)
    (IsOpen.preimage (Scheme.Hom.continuous f) V.is_open')
/- `U` is isomorphic to the prime spectrum of `R`. --/
  U_affine : X.toLocallyRingedSpace.restrict U.openEmbedding ≅ Spec.toLocallyRingedSpace.obj
    (Opposite.op R)
/- `V` is isomorphic to the prime spectrum of `S`. --/
  V_affine : Y.toLocallyRingedSpace.restrict V.openEmbedding ≅ Spec.toLocallyRingedSpace.obj
    (Opposite.op S)
/- The canonical ring homomorphism from `S` to `R` is smooth. --/
  is_smooth :
    let this : X.presheaf.obj (Opposite.op (TopologicalSpace.Opens.mk
      (f.val.base ⁻¹' V.carrier) (IsOpen.preimage (Scheme.Hom.continuous f) V.is_open'))) ⟶
      X.presheaf.obj (Opposite.op U.obj) := X.presheaf.map (CategoryTheory.opHomOfLE le_preimage)
    RingHom.IsSmooth (RingHom.comp this (f.val.c.1 (Opposite.op V)))

/--
Smooth morphisms of schemes.
-/
def Scheme.IsSmooth {X Y : Scheme} (f : X ⟶ Y) : Type _ := ∀ (x : X.toTopCat), IsSmoothAt f x

end Smooth
