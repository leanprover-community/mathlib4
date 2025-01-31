/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Order.Disjointed

/-!
# Uniform approximation by locally constant functions

We show that if `X` is a profinite space, and `V` is a uniform space, then any continuous function
`X → V` can be uniformly approximated by locally constant functions.
-/

open Metric UniformSpace Set

open TopologicalSpace (Opens Clopens)

open scoped Uniformity Function

namespace ContinuousMap

variable {ι X V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [UniformSpace V] (f : C(X, V)) {S : Set (V × V)}

/--
For any continuous function on `X` and `S ∈ 𝓤 V`, there exists a finite cover of `X` by
pairwise-disjoint nonempty clopens, on each of which `f` varies within `S`.
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_uniformity (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (D : Fin n → Clopens X), (∀ i, D i ≠ ⊥) ∧
    (∀ i, ∀ y ∈ D i, ∀ z ∈ D i, (f y, f z) ∈ S) ∧ (univ : Set X) ⊆ ⋃ i, ↑(D i) ∧
    Pairwise (Disjoint on D) := by
  -- Find a neighbourhood of each point on which `f` varies within `S`
  have step1 (x) : ∃ U : Opens X, x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U, (f y, f z) ∈ S := by
    obtain ⟨R, hR, hR', hRS⟩ := comp_symm_of_uniformity hS
    obtain ⟨U, hUB, hUo, hUx⟩ := mem_nhds_iff.mp <|  (f.continuousAt x).preimage_mem_nhds
      <| UniformSpace.ball_mem_nhds _ hR
    exact ⟨⟨U, hUo⟩, hUx, fun y hy z hz ↦ hRS <| prod_mk_mem_compRel (hR' <| hUB hy) (hUB hz)⟩
  choose U hUx hUS using step1
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ :=
    CompactSpace.exists_finite_nonempty_disjoint_clopen_cover_of_open_cover
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hUx x⟩)
  refine ⟨n, W, fun j ↦ (hW₁ j).1, fun j y hy z hz ↦ ?_, hW₂, hW₃⟩
  obtain ⟨i, hi⟩ := (hW₁ j).2
  refine hUS i y ?_ z ?_ <;>
  simpa using hi ‹_›

/--
Any continuous function from a profinite space to a uniform space can be uniformly approximated
by a function factoring through `Fin n`, for some `n`.
-/
lemma exists_fin_comp_of_mem_uniformity (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : X → Fin n) (h : Fin n → V), Continuous g ∧ ∀ x, (f x, h (g x)) ∈ S := by
  classical
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_uniformity f hS
  have h_uniq (x) : ∃! i, x ∈ E i := by
    refine match Set.mem_iUnion.mp (hEuniv <| mem_univ x) with | ⟨i, hi⟩ => ⟨i, hi, fun j hj ↦ ?_⟩
    refine Set.PairwiseDisjoint.elim (fun u _ v _ huv ↦ hEdis huv)
      (Set.mem_univ j) (Set.mem_univ i) ?_
    simp only [Disjoint, not_forall, le_bot_iff, ← SetLike.coe_set_eq, Clopens.coe_bot,
      ← nonempty_iff_ne_empty]
    exact ⟨E i ⊓ E j, inf_le_right, inf_le_left, x, by simp_all⟩
  choose g hg hg' using h_uniq
  have h_ex (i) : ∃ x, x ∈ E i := by
    simpa [← SetLike.coe_set_eq, ← nonempty_iff_ne_empty] using hEne i
  choose r hr using h_ex
  refine ⟨n, g, f ∘ r, continuous_discrete_rng.mpr fun j ↦ ?_, fun x ↦ (hES _) _ (hg _) _ (hr _)⟩
  convert (E j).isOpen
  exact Set.ext fun x ↦ ⟨fun hj ↦ hj ▸ hg x, fun hx ↦ (hg' _ _ hx).symm⟩

/--
If `f` is a continuous map from a profinite space to a uniform space with a group structure, then
we can uniformly approximate `f` by finite products of indicator functions of clopen sets.
-/
@[to_additive "If `f` is a continuous map from a profinite space to a uniform space with an
additive group structure, then we can uniformly approximate `f` by finite sums of indicator
functions of clopen sets."]
lemma exists_sum_const_mulIndicator_approx [CommGroup V] (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (U : Fin n → Clopens X) (v : Fin n → V),
    ∀ x, (f x, ∏ n, mulIndicator (U n) (fun _ ↦ v n) x) ∈ S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_fin_comp_of_mem_uniformity f hS
  refine ⟨n, fun i ↦ ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x ↦ ?_⟩
  convert hgh x
  exact (Fintype.prod_eq_single _ fun i hi ↦ mulIndicator_of_not_mem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

variable
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [AddCommGroup V] [UniformAddGroup V]
  {R : Type*} [TopologicalSpace R] [MonoidWithZero R] [MulActionWithZero R V]

/-- A continuous function on `X × Y` can be uniformly approximated by functions of the form
`f x • g y`. -/
lemma exists_sum_smul_approx (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x • h i y) ∈ S := by
  have hS' : {(f, g) | ∀ y, (f y, g y) ∈ S} ∈ 𝓤 C(Y, V) :=
    (ContinuousMap.mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_sum_const_indicator_approx f.curry hS'
  refine ⟨n, fun i ↦ ⟨_, (U i).isClopen.continuous_indicator <| continuous_const (y := 1)⟩,
    v, fun x y ↦ ?_⟩
  convert hv x y using 2
  simp only [ContinuousMap.sum_apply]
  congr 1 with i
  by_cases hi : x ∈ U i <;> simp [hi]

/-- A continuous function on `X × Y` can be uniformly approximated by functions of the form
`f x * g y`. -/
lemma exists_sum_mul_approx {𝕜 : Type*} [NormedRing 𝕜] (f : C(X × Y, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (g : Fin n → C(X, 𝕜)) (h : Fin n → C(Y, 𝕜)),
    ‖f - ∑ i, (g i).comp .fst * (h i).comp .snd‖ < ε := by
  obtain ⟨n, g, h, hfg⟩ := exists_sum_smul_approx (R := 𝕜) f (Metric.dist_mem_uniformity hε)
  refine ⟨n, g, h, ?_⟩
  simp only [ContinuousMap.norm_lt_iff _ hε]
  intro (x, y)
  simpa [dist_eq_norm_sub] using hfg x y

end ContinuousMap
