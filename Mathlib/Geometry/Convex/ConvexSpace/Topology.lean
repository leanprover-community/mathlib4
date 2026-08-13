/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# The topology on the standard simplex

In this file, we define a topology on the standard simplex `StdSimplex R M`.
When `M` is finite, this is the topology that is induced by the
embedding `StdSimplex R M → (M → R)`. In general, we use the supremum of
the coinduced topologies for the maps `StdSimplex.map f : StdSimplex R ι → StdSimplex R M`
where `f : ι → M` is a map from a finite set `ι`.

-/

universe u v

open Topology

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace Convexity.StdSimplex

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
      ← Finset.sum_eq_of_subset (s₁ := { i₁ | f i₁ = i₂}) (by simp)
        _ (fun i₁ _ hi₁ ↦ Finsupp.single_eq_of_ne' (by simpa using hi₁))]
    refine Finset.sum_congr rfl (fun i₁ hi₁ ↦ ?_)
    obtain rfl : f i₁ = i₂ := by simpa using hi₁
    simp
  simp only [this]
  fun_prop

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- This is the topology on `StdSimplex R M` when `M` is a possibly
infinite type. The lemma `StdSimplex.continuous_iff` shows that
this topology is characterized by the fact that a map `f` from
`StdSimplex R M` is continuous iff for any map `g : ι → M`
with a finite `ι`, the composition `f ∘ map g : StdSimplex R ι → _`
is continuous, where `StdSimplex R ι` is equipped with the
topology that is induced by the embedding `StdSimplex R ι → (ι → R)`. -/
@[no_expose]
public noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

variable {R} in
public lemma continuous_iff
    {M : Type v} {T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔
      ∀ (ι : Type v) [Finite ι] (g : ι → M), Continuous (f ∘ map g) := by
  rw [continuous_iSup_dom]
  refine forall_congr' (fun ι ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun _ ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun M ↦ ?_)
  rw [continuous_coinduced_dom, topologicalSpace_eq]

@[fun_prop]
public lemma continuous_map {M : Type*} {N : Type v} (f : M → N) :
    Continuous (map (R := R) f) := by
  wlog h : Finite M generalizing M
  · rw [continuous_iff]
    intro ι _ g
    rw [← map_comp']
    exact this (f ∘ g) inferInstance
  have H {ι : Type v} [Finite ι] (g : ι → N) : Continuous (map (R := R) g) := by
    rw [continuous_iff_coinduced_le]
    refine le_trans ?_ (le_iSup _ ι)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ g)
    rw [topologicalSpace_eq]
  obtain ⟨ι, _, ⟨e⟩⟩ : ∃ (ι : Type v) (_ : Finite ι), Nonempty (M ≃ ι) :=
    ⟨_, inferInstance, ⟨(Finite.equivFin M).trans Equiv.ulift.{v}.symm⟩⟩
  have : Continuous (map (R := R) e) := by
    rw [topologicalSpace_eq, topologicalSpace_eq]
    apply topologicalSpaceInduced.continuous_map
  convert (H (f ∘ e.symm)).comp this
  rw [← map_comp', Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

open Classical in
/-- Same as `StdSimplex.continuous_iff` but we only consider inclusions of
finite subsets of `M` instead of all maps `ι → M` for arbitrary finite types `ι`. -/
public lemma continuous_iff'
    {M T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔ ∀ (s : Finset M), Continuous (f ∘ map (Subtype.val : s → M)) := by
  rw [continuous_iff]
  refine ⟨fun h s ↦ h _ _, fun h ι _ g ↦ ?_⟩
  have := Fintype.ofFinite ι
  have := (h (Finset.image g .univ)).comp (continuous_map R (fun i ↦ ⟨g i, by grind⟩))
  rwa [Function.comp_assoc, ← map_comp'] at this

open topologicalSpaceInduced in
@[fun_prop]
public lemma continuous_weights_apply {M : Type*} (m : M) :
    Continuous (fun (t : StdSimplex R M) ↦ t.weights m) := by
  rw [continuous_iff]
  intro ι _ g
  rw [topologicalSpace_eq]
  exact continuous_map_weights_apply R g m

public lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

public lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end Convexity.StdSimplex
