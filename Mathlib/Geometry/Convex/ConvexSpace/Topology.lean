/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# ...

-/

universe u v

-- to be moved
open Classical in
@[to_additive]
lemma Finset.prod_eq_of_subset {ι M : Type*} [CommMonoid M]
    {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) (f : ι → M) (hf : ∀ (i : ι), i ∈ s₂ → i ∉ s₁ → f i = 1) :
    ∏ i ∈ s₁, f i = ∏ i ∈ s₂, f i := by
  rw [show s₂ = s₁.disjUnion (s₂ \ s₁) disjoint_sdiff by simpa, Finset.prod_disjUnion,
    Finset.prod_eq_one (s := s₂ \ s₁) (by aesop), mul_one]

open Topology

namespace Convexity

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace StdSimplex

abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} [Finite ι] (i : ι) :
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
    simp only [weights_map, Finsupp.mapDomain]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [← Finset.sum_eq_of_subset (s₁ := { i₁ | f i₁ = i₂}) (by simp) _
      (fun i₁ _ hi₁ ↦ Finsupp.single_eq_of_ne' (by simpa using hi₁))]
    refine Finset.sum_congr rfl (fun i₁ hi₁ ↦ ?_)
    obtain rfl : f i₁ = i₂ := by simpa using hi₁
    simp
  simp only [this]
  fun_prop

lemma continuous_map
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
@[no_expose]
public noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M),
    TopologicalSpace.coinduced (map f) inferInstance

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [show map id = id by aesop]
    rfl

variable {R} in
lemma continuous_iff
    {M : Type v} {T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔ ∀ (ι : Type v) [Finite ι] (g : ι → M),
      Continuous (f ∘ map g) := by
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
public lemma continuous_iff'
    {M T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔ ∀ (s : Finset M),
      Continuous (f ∘ map (Subtype.val : s → M)) := by
  rw [continuous_iff]
  refine ⟨fun h s ↦ h _ _, fun h ι _ g ↦ ?_⟩
  have := Fintype.ofFinite ι
  have := (h (Finset.image g .univ)).comp (continuous_map R (fun i ↦ ⟨g i, by aesop⟩))
  rwa [Function.comp_assoc, ← map_comp'] at this

open topologicalSpaceInduced in
@[fun_prop]
lemma continuous_weights_apply {M : Type*} (m : M) :
    Continuous (fun (t : StdSimplex R M) ↦ t.weights m) := by
  rw [continuous_iff]
  intro ι _ g
  rw [topologicalSpace_eq]
  exact continuous_map_weights_apply R g m

-- to be moved
lemma range_toFun_comp_weights (M : Type*) [Fintype M] :
    Set.range (fun (t : StdSimplex R M) ↦ (t.weights : M → R)) =
    (⋂ (i : M), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s.weights_nonneg, ?_⟩
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this
  · rintro ⟨h₁, h₂⟩
    refine ⟨{ weights := ∑ (m : M), .single m (s m), nonneg := ?_, total := ?_ }, ?_⟩
    · intro m
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single m (by aesop) (by simp)]
      simpa using h₁ m
    · simp only [implies_true, Finsupp.sum_fintype, Finsupp.coe_finsetSum,
        Finset.sum_apply, ← h₂]
      congr
      ext m
      rw [Finset.sum_eq_single m (by aesop) (by simp), Finsupp.single_eq_same]
    · ext m
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single m (by aesop) (by simp), Finsupp.single_eq_same]

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    exact IsClosed.inter (isClosed_iInter
      (fun _ ↦ isClosed_le (by fun_prop) (by fun_prop)))
      (isClosed_eq (by fun_prop) (by fun_prop))

end StdSimplex

end Convexity
