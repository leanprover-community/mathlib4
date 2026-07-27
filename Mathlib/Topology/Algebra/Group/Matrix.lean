/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Instances.Matrix

/-!
# Topology on matrix groups

Lemmas about the topology of matrix groups, such as `GL(n, R)` and `SL(n, R)` for a
topological ring `R`.
-/

public section

open Matrix Topology

variable {n R S : Type*} [Fintype n] [DecidableEq n]
  [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S] {f : R →+* S}

/-!
### Topology of the general linear group
-/

namespace Matrix.GeneralLinearGroup

@[fun_prop]
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → GL n R) (hf : Continuous f) (i : n) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

@[fun_prop]
lemma _root_.Continuous.generalLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) :=
  (continuous_id.matrix_map hf).units_map

lemma _root_.Topology.IsInducing.generalLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  hf.matrix_map.units_map

lemma _root_.Topology.IsEmbedding.generalLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

variable [IsTopologicalRing R]

lemma _root_.Topology.IsClosedEmbedding.generalLinearGroup_map [T0Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  hf.matrix_map.units_map

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

/-!
### Topology of the special linear group
-/
namespace Matrix.SpecialLinearGroup

local notation "SL" => SpecialLinearGroup

instance : TopologicalSpace (SL n R) :=
  inferInstanceAs <| TopologicalSpace (Subtype _)

@[fun_prop]
theorem continuous_apply {α : Type*} [TopologicalSpace α]
    (f : α → SL n R) (hf : Continuous f) (i) :
    Continuous (fun x ↦ f x i) :=
  (by fun_prop : Continuous fun A : Matrix n n R ↦ A i).comp <| by fun_prop

/-- The topology on `SL n R` is functorial in `R`. -/
@[fun_prop]
lemma _root_.Continuous.specialLinearGroup_map (hf : Continuous f) :
    Continuous (map (n := n) f) := by
  refine IsInducing.subtypeVal.continuous_iff.mpr ?_
  exact (continuous_id.matrix_map hf).comp continuous_subtype_val

lemma _root_.Topology.IsInducing.specialLinearGroup_map (hf : IsInducing f) :
    IsInducing (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

lemma _root_.Topology.IsEmbedding.specialLinearGroup_map (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp .subtypeVal).of_comp (by fun_prop) continuous_subtype_val

variable [IsTopologicalRing R]

/-- If `R` is a commutative ring with the discrete topology, then `SL(n, R)` has the discrete
topology. -/
instance [DiscreteTopology R] : DiscreteTopology (SL n R) :=
  inferInstanceAs <| DiscreteTopology (Subtype _)

lemma isClosedEmbedding_val [T1Space R] :
    IsClosedEmbedding ((↑) : SL n R → Matrix n n R) :=
  (isClosed_singleton.preimage continuous_id.matrix_det).isClosedEmbedding_subtypeVal

lemma _root_.Topology.IsClosedEmbedding.specialLinearGroup_map [T1Space R]
    (hf : IsClosedEmbedding f) : IsClosedEmbedding (map (n := n) f) :=
  (hf.matrix_map.comp isClosedEmbedding_val).of_comp .subtypeVal

instance instT1Space [T1Space R] : T1Space (SL n R) := isClosedEmbedding_val.isEmbedding.t1Space

/-- The special linear group over a topological ring is a topological group. -/
instance topologicalGroup : IsTopologicalGroup (SL n R) where
  continuous_inv := continuous_induced_rng.mpr continuous_induced_dom.matrix_adjugate
  continuous_mul := continuous_induced_rng.mpr <|
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)

/-!
### Mapping `SL(n, R)` to `GL(n, R)`
-/
section toGL

/-- The natural map from `SL n A` to `GL n A` is continuous. -/
@[fun_prop]
lemma continuous_toGL : Continuous (toGL : SL n R → GL n R) := by
  simp_rw [Units.continuous_iff, ← map_inv]
  constructor <;> fun_prop

/-- The natural map from `SL n A` to `GL n A` is inducing, i.e. the topology on
`SL n A` is the pullback of the topology from `GL n A`. -/
lemma isInducing_toGL : IsInducing (toGL : SL n R → GL n R) :=
  .of_comp continuous_toGL Units.continuous_val (IsInducing.induced _)

/-- The natural map from `SL n A` in `GL n A` is an embedding, i.e. it is an injection and
the topology on `SL n A` coincides with the subspace topology from `GL n A`. -/
lemma isEmbedding_toGL : IsEmbedding (toGL : SL n R → GL n R) :=
  ⟨isInducing_toGL, toGL_injective⟩

theorem range_toGL {A : Type*} [CommRing A] :
    Set.range (toGL : SL n A → GL n A) = GeneralLinearGroup.det ⁻¹' {1} := by
  ext x
  simpa [Units.ext_iff] using ⟨fun ⟨y, hy⟩ ↦ by simp [← hy], fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The natural inclusion of `SL n A` in `GL n A` is a closed embedding. -/
lemma isClosedEmbedding_toGL [T0Space R] : IsClosedEmbedding (toGL : SL n R → GL n R) :=
  ⟨isEmbedding_toGL, by simpa [range_toGL] using isClosed_singleton.preimage <| by fun_prop⟩

end toGL

section mapGL

/-!
### Shortcuts for the composite `SL(n, R) → GL(n, S)`
-/
variable [Algebra R S] [IsTopologicalRing S]

omit [IsTopologicalRing R]

lemma continuous_mapGL [ContinuousSMul R S] : Continuous (mapGL S : SL n R → _) :=
  continuous_toGL.comp
    (continuous_algebraMap_iff_smul R S |>.2 continuous_smul).specialLinearGroup_map

lemma isInducing_mapGL (h : IsInducing (algebraMap R S)) :
    IsInducing (mapGL S : SL n R → _) :=
  isInducing_toGL.comp h.specialLinearGroup_map

lemma isEmbedding_mapGL (h : IsEmbedding (algebraMap R S)) :
    IsEmbedding (mapGL S : SL n R → _) :=
  isEmbedding_toGL.comp h.specialLinearGroup_map

lemma isClosedEmbedding_mapGL [IsTopologicalRing R] [T1Space R] [T1Space S]
    (h : IsClosedEmbedding (algebraMap R S)) :
    IsClosedEmbedding (mapGL S : SL n R → _) :=
  isClosedEmbedding_toGL.comp h.specialLinearGroup_map

end mapGL

end Matrix.SpecialLinearGroup

end
