/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Topology.Spectral.Hom
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Connected and irreducible morphisms

-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A scheme `X` over a field `K` is geometrically connected, if it remains connected after base
changing along arbitrary field extensions of `K`. -/
class IsGeometricallyConnected (f : X ⟶ Spec (.of K)) : Prop where
  pullback_connectedSpace_of_field {L : Type u} [Field L] (i : CommRingCat.of K ⟶ .of L) :
    ConnectedSpace ↑(pullback f (Spec.map i))

/-- A scheme `X` over a field `K` is geometrically irreducible, if it remains irreducible after base
changing along arbitrary field extensions of `K`. -/
class IsGeometricallyIrreducible (f : X ⟶ Spec (.of K)) : Prop where
  pullback_irreducibleSpace_of_field {L : Type u} [Field L] (i : CommRingCat.of K ⟶ .of L) :
    IrreducibleSpace ↑(pullback f (Spec.map i))

variable {Y : Scheme.{u}}

/-- The morphism from the fiber of `f` over `y` to the spectrum of the residue field of `y`. -/
noncomputable def fiber (f : X ⟶ Y) (y : Y) :
    pullback f (Y.fromSpecResidueField y) ⟶ Spec (.of <| Y.residueField y) :=
  pullback.snd _ _

/-- A morphism is connnected if its fibers are geometrically connected. -/
class IsConnected (f : X ⟶ Y) : Prop where
  fiber_isGeometricallyConnected (y : Y) : IsGeometricallyConnected (fiber f y)

/-- A morphism is connnected if its fibers are geometrically irreducible. -/
class IsIrreducible (f : X ⟶ Y) : Prop where
  fiber_isGeometricallyConnected (y : Y) : IsGeometricallyIrreducible (fiber f y)

end AlgebraicGeometry
