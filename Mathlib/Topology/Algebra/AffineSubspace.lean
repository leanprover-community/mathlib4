/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Algebra.Group.AddTorsor

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

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

instance {s : AffineSubspace R P} [Nonempty s] : IsTopologicalAddTorsor s where
  continuous_vadd := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop
  continuous_vsub := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop

theorem isClosed_direction_iff [T1Space V] (s : AffineSubspace R P) :
    IsClosed (s.direction : Set V) ↔ IsClosed (s : Set P) := by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image,
    AffineSubspace.coe_direction_eq_vsub_set_right hx]
  simp only [Homeomorph.vaddConst_symm_apply]

end AffineSubspace
