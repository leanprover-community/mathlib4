/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-! # Smooth manifolds as locally ringed spaces

This file equips a smooth manifold with the structure of a locally ringed space.

## Main results

* `smoothSheafCommRing.isUnit_stalk_iff`: The units of the stalk at `x` of the sheaf of smooth
  functions from a smooth manifold `M` to its scalar field `𝕜`, considered as a sheaf of commutative
  rings, are the functions whose values at `x` are nonzero.

## Main definitions

* `IsManifold.locallyRingedSpace`: A smooth manifold can be considered as a locally ringed space.

## TODO

Characterize morphisms-of-locally-ringed-spaces (`AlgebraicGeometry.LocallyRingedSpace.Hom`) between
smooth manifolds.

-/

noncomputable section
universe u
