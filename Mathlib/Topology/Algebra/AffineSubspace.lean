/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Topology of affine subspaces.

This file defines the embedding map from an affine subspace to the ambient space as a continuous
affine map.

## Main definitions

* `AffineSubspace.subtypeA` is `AffineSubspace.subtype` as a `ContinuousAffineMap`.

-/


namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

/-- Embedding of an affine subspace to the ambient space, as a continuous affine map. -/
def subtypeA (s : AffineSubspace R P) [Nonempty s] : s →ᴬ[R] P where
  toAffineMap := s.subtype
  cont := continuous_subtype_val

@[simp] lemma coe_subtypeA (s : AffineSubspace R P) [Nonempty s] : ⇑s.subtypeA = Subtype.val :=
  rfl

@[simp] lemma subtypeA_toAffineMap (s : AffineSubspace R P) [Nonempty s] :
    s.subtypeA.toAffineMap = s.subtype :=
  rfl

end AffineSubspace
