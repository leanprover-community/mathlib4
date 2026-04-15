/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Instances.Matrix

/-!
# Topology on matrix groups

Lemmas about the topology of matrix groups, such as `GL(n, R)` and `SL(n, R)` for a
topological ring `R`.
-/

@[expose] public section

open Matrix

variable {n R : Type*}

/-! ### Lemmas about matrix groups -/

section MatrixGroups

variable [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace Matrix.GeneralLinearGroup

omit [IsTopologicalRing R] in
@[fun_prop]
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → GL n R) (hf : Continuous f) (i : n) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

/-- The determinant is continuous as a map from the general linear group to the units. -/
@[continuity, fun_prop] protected lemma continuous_det :
    Continuous (det : GL n R → Rˣ) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

@[continuity, fun_prop]
lemma continuous_upperRightHom {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (upperRightHom (R := R)) := by
  simp only [continuous_induced_rng, Function.comp_def, upperRightHom_apply,
    Units.embedProduct_apply, Units.inv_mk, continuous_prodMk, MulOpposite.unop_op]
  constructor <;>
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_neg, continuous_id']

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

local notation "SL" => SpecialLinearGroup

omit [IsTopologicalRing R] in
instance : TopologicalSpace (SL n R) :=
  inferInstanceAs <| TopologicalSpace (Subtype _)

omit [IsTopologicalRing R] in
@[fun_prop]
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → SL n R) (hf : Continuous f) (i) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

/-- If `R` is a commutative ring with the discrete topology, then `SL(n, R)` has the discrete
topology. -/
instance [DiscreteTopology R] : DiscreteTopology (SL n R) :=
  inferInstanceAs <| DiscreteTopology (Subtype _)

lemma isClosedEmbedding_val [T1Space R] :
    Topology.IsClosedEmbedding ((↑) : SL n R → Matrix n n R) :=
  (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal

set_option backward.isDefEq.respectTransparency false in
/-- The special linear group over a topological ring is a topological group. -/
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := by simpa [continuous_induced_rng] using continuous_induced_dom.matrix_adjugate
  continuous_mul := by simpa only [continuous_induced_rng] using
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

section toGL -- results on the map from `SL` to `GL`

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
lemma continuous_toGL : Continuous (toGL : SL n R → GL n R) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/-- The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`. -/
lemma isInducing_toGL : Topology.IsInducing (toGL : SL n R → GL n R) :=
  .of_comp continuous_toGL Units.continuous_val (Topology.IsInducing.induced _)

/-- The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injection and
the topology on `SL n A` coincides with the subspace topology from `GL n A`. -/
lemma isEmbedding_toGL : Topology.IsEmbedding (toGL : SL n R → GL n R) :=
  ⟨isInducing_toGL, toGL_injective⟩

theorem range_toGL {A : Type*} [CommRing A] :
    Set.range (toGL : SL n A → GL n A) = GeneralLinearGroup.det ⁻¹' {1} := by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The natural inclusion of `SL n A` in `GL n A` is a closed embedding. -/
lemma isClosedEmbedding_toGL [T0Space R] : Topology.IsClosedEmbedding (toGL : SL n R → GL n R) :=
  ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage <| by fun_prop⟩

end toGL

section mapGL

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

set_option backward.isDefEq.respectTransparency false in
lemma isInducing_mapGL (h : Topology.IsInducing (algebraMap A B)) :
    Topology.IsInducing (mapGL B : SL n A → GL n B) := by
  -- TODO: add `IsInducing.units_map` and deduce `IsInducing.generalLinearGroup_map`
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

end MatrixGroups
