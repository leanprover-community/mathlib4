/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Instances.Matrix

/-!
# Topology of the general linear group
-/

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The determinant is continuous as a map from the general linear group to the units. -/
@[continuity, fun_prop] protected lemma Matrix.GeneralLinearGroup.continuous_det :
    Continuous (det : GL n A → Aˣ) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

namespace Matrix.SpecialLinearGroup -- results on the map from `SL` to `GL`

local notation "SL" => SpecialLinearGroup

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
lemma continuous_toGL : Continuous (toGL : SL n A → GL n A) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/-- The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`. -/
lemma isInducing_toGL : Topology.IsInducing (toGL : SL n A → GL n A) :=
  .of_comp continuous_toGL Units.continuous_val (Topology.IsInducing.induced _)

/-- The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injection and
the topology on `SL n A` coincides with the subspace topology from `GL n A`. -/
lemma isEmbedding_toGL : Topology.IsEmbedding (toGL : SL n A → GL n A) :=
  ⟨isInducing_toGL, toGL_injective⟩

lemma isClosed_range_toGL [T0Space A] : IsClosed (Set.range (toGL : SL n A → GL n A)) := by
  convert_to IsClosed (GeneralLinearGroup.det ⁻¹' {1})
  · ext x
    simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  · apply isClosed_singleton.preimage GeneralLinearGroup.continuous_det

/-- The natural inclusion of `SL n A` in `GL n A` is a closed embedding. -/
lemma isClosedEmbedding_toGL [T0Space A] : Topology.IsClosedEmbedding (toGL : SL n A → GL n A) :=
  ⟨isEmbedding_toGL, isClosed_range_toGL⟩

section mapGL

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

lemma isInducing_mapGL (h : Topology.IsInducing (algebraMap A B)) :
    Topology.IsInducing (mapGL B : SL n A → GL n B) := by
  refine isInducing_toGL.comp ?_
  refine .of_comp ?_ continuous_induced_dom (h.matrix_map.comp (Topology.IsInducing.induced _))
  rw [continuous_induced_rng]
  exact continuous_subtype_val.matrix_map h.continuous

lemma isEmbedding_mapGL (h : Topology.IsEmbedding (algebraMap A B)) :
    Topology.IsEmbedding (mapGL B : SL n A → GL n B) :=
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).mpr h.2
  ⟨isInducing_mapGL h.isInducing, mapGL_injective⟩

end mapGL

end Matrix.SpecialLinearGroup
