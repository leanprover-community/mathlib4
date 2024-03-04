/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Topology.Algebra.Ring.Basic

#align_import topology.algebra.localization from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`Localization M` endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at an `M`.

## Main Results

- `Localization.ringTopology`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/


variable {R : Type*} [CommRing R] [TopologicalSpace R] {M : Submonoid R}

/-- The ring topology on `Localization M` coinduced from the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)`. -/
def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun
#align localization.ring_topology Localization.ringTopology

instance : TopologicalSpace (Localization M) :=
  Localization.ringTopology.toTopologicalSpace

instance : TopologicalRing (Localization M) :=
  Localization.ringTopology.toTopologicalRing
