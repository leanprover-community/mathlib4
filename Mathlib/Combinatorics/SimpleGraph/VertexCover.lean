/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

import Mathlib.Data.Finite.Card
import Mathlib.Tactic.ENatToNat

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G c`: Predicate that `c` is a vertex cover of `G`.
* `SimpleGraph.vertexCoverNum G`: The vertex cover number, e.g. the size of a minimal vertex cover.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

/-- `c` is a vertex cover of `G` if every edge in `G` is incident to at least one vertex in `c`. -/
def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → v ∈ c ∨ w ∈ c

@[simp]
theorem isVertexCover_empty : IsVertexCover G ∅ ↔ G = ⊥ := by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

@[simp]
theorem isVertexCover_univ : IsVertexCover G .univ := by
  simp [IsVertexCover]

@[simp]
theorem isVertexCover_bot (c : Set V) : IsVertexCover ⊥ c := by
  simp [IsVertexCover]

theorem IsVertexCover.subset {c d : Set V} (hcd : c ⊆ d) (hc : IsVertexCover G c) :
    IsVertexCover G d := by
  grind [IsVertexCover]

theorem IsVertexCover.mono {c : Set V} (hG : G ≤ G') (hc : IsVertexCover G' c) :
    IsVertexCover G c :=
  fun _ _ hadj ↦ hc (hG hadj)

/-- A set `c` is a vertex cover iff the complement of `c` is an independent set. -/
@[simp]
theorem isIndepSet_compl_iff_isVertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVertexCover G c := by
  refine ⟨fun hi v w hadj ↦ ?_, by grind [IsVertexCover, Set.Pairwise]⟩
  by_contra! hh
  exact hi hh.1 hh.2 (Adj.ne hadj) hadj

@[simp]
theorem isVertexCover_compl {c : Set V} : G.IsVertexCover cᶜ ↔ G.IsIndepSet c := by
  simp [← isIndepSet_compl_iff_isVertexCover]

theorem IsVertexCover.preimage {F : Type*} [FunLike F V W] [HomClass F G H]
    (f : F) {c : Set W} (hc : IsVertexCover H c) :
    IsVertexCover G (f ⁻¹' c) :=
  fun _ _ hadj ↦ hc (map_rel f hadj)

@[simp]
theorem isVertexCover_preimage_iso (f : G ≃g H) {c : Set W} :
    IsVertexCover G (f ⁻¹' c) ↔ IsVertexCover H c where
  mp h := by
    simpa [← RelIso.image_eq_preimage_symm, Set.image_preimage_eq _ f.surjective]
      using h.preimage f.symm
  mpr := .preimage f

@[simp]
theorem isVertexCover_image_iso (f : G ≃g H) {c : Set V} :
    IsVertexCover H (f '' c) ↔ IsVertexCover G c := by
  simp [RelIso.image_eq_preimage_symm]

end IsVertexCover

section vertexCoverNum

/-- The vertex cover number of `G` is the minimal number of vertices in a vertex cover of `G`. -/
noncomputable def vertexCoverNum (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (s : Set V) (_ : IsVertexCover G s), s.encard

theorem vertexCoverNum_le_iff {n : ℕ∞} :
    vertexCoverNum G ≤ n ↔ ∀ (m : ℕ∞), (∀ s, IsVertexCover G s → m ≤ s.encard) → m ≤ n := by
  simp [vertexCoverNum, iInf_le_iff]

theorem IsVertexCover.vertexCoverNum_le {c : Set V} (hc : IsVertexCover G c) :
    vertexCoverNum G ≤ c.encard :=
  vertexCoverNum_le_iff.mpr fun _ hm ↦ hm c hc

theorem vertexCoverNum_exists (G) :
    ∃ s : Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s := by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs ▸ iInf_subtype, s.property⟩

theorem exists_of_le_vertexCoverNum (n : ℕ) (h₁ : vertexCoverNum G ≤ n)
    (h₂ : n ≤ ENat.card V) : ∃ s : Set V, s.encard = n ∧ IsVertexCover G s := by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.subset hr₁⟩

@[simp]
theorem vertexCoverNum_bot : vertexCoverNum (emptyGraph V) = 0 :=
  nonpos_iff_eq_zero.mp <| Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]
theorem vertexCoverNum_of_subsingleton [Subsingleton V] : vertexCoverNum G = 0 := by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]
theorem vertexCoverNum_eq_zero : vertexCoverNum G = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  simpa [h] using vertexCoverNum_exists G

theorem vertexCoverNum_le_card_sub_one : vertexCoverNum G ≤ ENat.card V - 1 := by
  nontriviality V
  obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V) |>.to_nonempty
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_diff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]
theorem vertexCoverNum_ne_top_of_finite [Finite V] : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)

theorem vertexCoverNum_lt_card [Nonempty V] [Finite V] : vertexCoverNum G < ENat.card V := by
  refine (ENat.add_one_le_iff vertexCoverNum_ne_top_of_finite).mp ?_
  grw [vertexCoverNum_le_card_sub_one, ENat.card_eq_coe_natCard]
  enat_to_nat
  exact Nat.add_le_of_le_sub (Order.one_le_iff_pos.mpr Nat.card_pos) (le_refl _)

theorem vertexCoverNum_le_encard_edgeSet : vertexCoverNum G ≤ G.edgeSet.encard := by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn ((·.out.1) '' G.edgeSet)
    (fun v w _ ↦ by grind [Sym2.out_fst_mem s(v, w), mem_edgeSet])
  grind [Set.encard_image_le]

@[simp]
theorem vertexCoverNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) vertexCoverNum_le_encard_edgeSet

@[simp]
theorem vertexCoverNum_top : vertexCoverNum (completeGraph V) = ENat.card V - 1 := by
  nontriviality V using tsub_eq_zero_of_le
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  by_contra! hh
  have : n - 1 ≤ ENat.card V := by
    grw [tsub_le_iff_right, hn]
    simp [add_assoc, one_add_one_eq_two]
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_le_vertexCoverNum (n - 1) (ENat.le_sub_one_of_lt hh) this
  have : 1 < (Set.univ \ t).encard := by
    refine ENat.add_one_le_iff (by simp) |>.mp ?_
    rw [Set.encard_diff (by simp) (Set.finite_of_encard_eq_coe ht₁), Set.encard_univ]
    refine ENat.le_sub_of_add_le_left (by simp [ht₁]) ?_
    refine add_le_of_le_tsub_right_of_le (Order.add_one_le_of_lt ENat.one_lt_card) ?_
    grw [ht₁, ENat.coe_sub, hn]
    simp [add_assoc, one_add_one_eq_two, le_tsub_add]
  obtain ⟨a, b, _, _, hne⟩ := Set.one_lt_encard_iff.mp <| this
  have := @ht₂ a b (by simp [hne])
  grind

theorem IsContained.vertexCoverNum_le_vertexCoverNum (h : G ⊑ H) :
    vertexCoverNum G ≤ vertexCoverNum H := by
  have ⟨f, hf⟩ := h
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
  have := H.isIndepSet_iff_isAntichain_adj.mp <| isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj ↦ f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
    isIndepSet_compl_iff_isVertexCover.mp <| G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
  exact Function.Embedding.encard_le <| Function.Embedding.mk f hf |>.subtypeMap (by simp)

@[deprecated IsContained.vertexCoverNum_le_vertexCoverNum (since := "2026-01-07")]
theorem vertexCoverNum_le_vertexCoverNum_of_injective (f : G →g H) (hf : Function.Injective f) :
    vertexCoverNum G ≤ vertexCoverNum H :=
  IsContained.vertexCoverNum_le_vertexCoverNum ⟨f, hf⟩

@[gcongr]
theorem vertexCoverNum_mono (h : G ≤ G') : vertexCoverNum G ≤ vertexCoverNum G' :=
  (IsContained.of_le h).vertexCoverNum_le_vertexCoverNum

theorem vertexCoverNum_congr (f : G ≃g H) : vertexCoverNum G = vertexCoverNum H :=
  le_antisymm f.isContained.vertexCoverNum_le_vertexCoverNum
    f.symm.isContained.vertexCoverNum_le_vertexCoverNum

end vertexCoverNum
end SimpleGraph
