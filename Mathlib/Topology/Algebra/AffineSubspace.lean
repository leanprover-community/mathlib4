/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Restrict
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import Mathlib.Topology.Algebra.Group.AddTorsor

/-!
# Topology of affine subspaces.

This file defines the embedding map from an affine subspace to the ambient space as a continuous
affine map.

## Main definitions

* `AffineSubspace.subtypeA` is `AffineSubspace.subtype` as a `ContinuousAffineMap`.

-/

@[expose] public section


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

/-- Equal affine subspaces are continuously affinely equivalent. -/
noncomputable def congr {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) : s ≃ᴬ[R] t where
  toEquiv := Equiv.setCongr (congrArg ((↑) : AffineSubspace R P → Set P) h)
  linear := LinearEquiv.ofEq _ _ (congrArg AffineSubspace.direction h)
  map_vadd' := by
    subst h
    intro _ _
    rfl
  continuous_toFun := by
    subst h; exact continuous_id
  continuous_invFun := by
    subst h; exact continuous_id

@[simp]
theorem coe_congr_apply {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) (x : s) : (congr h x : P) = x := by
  subst h; rfl

variable {W Q : Type*} [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/-- A continuous affine equivalence restricts to a continuous affine equivalence between an affine
subspace and its image. -/
noncomputable def continuousAffineEquivMap (s : AffineSubspace R P) [Nonempty s]
    (e : P ≃ᴬ[R] Q) : s ≃ᴬ[R] s.map e.toAffineMap :=
  let e' : s ≃ᵃ[R] s.map e.toAffineMap :=
    AffineEquiv.ofBijective (AffineMap.restrict.bijective (E := s) e.injective)
  { e' with
    continuous_toFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using
      (e.continuous.comp continuous_subtype_val).congr fun _ => rfl
    continuous_invFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using
      (e.continuous_invFun.comp continuous_subtype_val).congr fun x ↦
        (e.apply_eq_iff_eq_symm_apply.mp (congrArg Subtype.val (e'.apply_symm_apply x))).symm }

@[simp]
theorem continuousAffineEquivMap_apply {s : AffineSubspace R P} [Nonempty s]
    (e : P ≃ᴬ[R] Q) (x : s) : s.continuousAffineEquivMap e x = e x := rfl

@[simp]
theorem continuousAffineEquivMap_apply_symm_apply {s : AffineSubspace R P} [Nonempty s]
    (e : P ≃ᴬ[R] Q) (x : s.map e.toAffineMap) :
    e ((s.continuousAffineEquivMap e).symm x) = x :=
  congrArg Subtype.val <| (s.continuousAffineEquivMap e).apply_symm_apply x

end AffineSubspace

namespace ContinuousAffineEquiv

variable {R V P W Q : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P] [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/-- A continuous affine equivalence induces a continuous affine equivalence between the affine span
of a nonempty set and the affine span of its image. -/
noncomputable def affineSpanImageEquiv (e : P ≃ᴬ[R] Q) (s : Set P) [Nonempty s] :
    (affineSpan R s) ≃ᴬ[R] (affineSpan R (e '' s)) :=
  ((affineSpan R s).continuousAffineEquivMap e).trans <|
    AffineSubspace.congr (AffineSubspace.map_span e.toAffineMap s)

@[simp]
theorem affineSpanImageEquiv_apply (e : P ≃ᴬ[R] Q) (s : Set P) [Nonempty s]
    (x : affineSpan R s) : (e.affineSpanImageEquiv s x : Q) = e x :=
  (AffineSubspace.coe_congr_apply (AffineSubspace.map_span e.toAffineMap s)
    (((affineSpan R s).continuousAffineEquivMap e) x)).trans
    (AffineSubspace.continuousAffineEquivMap_apply e x)

end ContinuousAffineEquiv

namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

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
