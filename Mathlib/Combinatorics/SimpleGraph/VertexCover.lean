/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G C`: Predicate that `C` is a vertex cover of `G`.
* `SimpleGraph.vertexCoverNum G`: The vertex cover number, e.g. the size of a minimal vertex cover.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

/-- `C` is a vertex cover of `G` if every edge in `G` is incident to at least one vertex in `C`. -/
def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → v ∈ c ∨ w ∈ c

@[simp]
theorem isVertexCover_empty : IsVertexCover G ∅ ↔ G = ⊥ := by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

theorem not_isVertexCover_of_ne_bot (h : G ≠ ⊥) : ¬IsVertexCover G ∅ :=
  iff_false_right h |>.mp isVertexCover_empty

@[simp]
theorem isVertexCover_univ : IsVertexCover G .univ := by
  simp [IsVertexCover]

@[simp]
theorem isVertexCover_bot (c : Set V) : IsVertexCover ⊥ c := by
  simp [IsVertexCover]

theorem IsVertexCover.mono (c d : Set V) (hcd : c ⊆ d) (hc : IsVertexCover G c) :
    IsVertexCover G d := by
  grind [IsVertexCover]

/-- A set `c` is a vertex cover iff the complement of `c` is an independent set. -/
@[simp]
theorem isIndepSet_compl_iff_isVertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVertexCover G c := by
  constructor
  · intro hi v w hadj
    by_cases hh : v ∈ c ∨ w ∈ c
    · grind
    · rw [not_or] at hh
      exact False.elim <| hi hh.1 hh.2 (Adj.ne hadj) hadj
  · grind [IsVertexCover, Set.Pairwise]

@[simp]
theorem isVertexCover_compl {c : Set V} : G.IsVertexCover cᶜ ↔ G.IsIndepSet c := by
  simp [← isIndepSet_compl_iff_isVertexCover]

theorem IsVertexCover.preimage {F : Type*} [FunLike F V W] [RelHomClass F G.Adj H.Adj]
    (f : F) {c : Set W} (hc : IsVertexCover H c) :
    IsVertexCover G (f ⁻¹' c) :=
  fun _ _ hadj ↦ hc (map_rel f hadj)

theorem isVertexCover_iff_of_relIso (f : G ≃g H) (c : Set V) :
    IsVertexCover G c ↔ IsVertexCover H (f '' c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [RelIso.image_eq_preimage_symm]
    exact h.preimage f.symm.toHom
  · have := h.preimage f.toHom
    simpa [RelIso.image_eq_preimage_symm, Set.preimage_preimage] using this

end IsVertexCover

section vertexCoverNum

/-- The vertex cover number of `G` is the minimal number of vertices in a vertex cover of `G`. -/
noncomputable def vertexCoverNum (G : SimpleGraph V) : ℕ∞ :=
  ⨅ s : {s : Set V // IsVertexCover G s}, s.val.encard

theorem IsVertexCover.vertexCoverNum_le {c : Set V} (hc : IsVertexCover G c) :
    vertexCoverNum G ≤ c.encard :=
  iInf_le_iff.mpr fun _ hn ↦ hn ⟨c, hc⟩

theorem vertexCoverNum_exists (G) :
    ∃ s : Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s := by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs, s.property⟩

theorem exists_of_le_vertexCoverNum (n : ℕ) (h₁ : vertexCoverNum G ≤ n)
    (h₂ : n ≤ ENat.card V) : ∃ s : Set V, s.encard = n ∧ IsVertexCover G s := by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.mono s r hr₁⟩

@[simp]
theorem vertexCoverNum_bot : vertexCoverNum (emptyGraph V) = 0 :=
  nonpos_iff_eq_zero.mp <| Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]
theorem vertexCoverNum_of_subsingleton [Subsingleton V] : vertexCoverNum G = 0 := by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]
theorem vertexCoverNum_eq_zero : vertexCoverNum G = 0 ↔ G = ⊥ := by
  constructor
  · intro h
    have := vertexCoverNum_exists G
    simp_all
  · simp_all

theorem vertexCoverNum_le_card_sub_one : vertexCoverNum G ≤ ENat.card V - 1 := by
  nontriviality V
  obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V) |>.to_nonempty
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff, Subtype.forall] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_diff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]
theorem vertexCoverNum_ne_top_of_finite [Finite V] : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)

theorem vertexCoverNum_le_encard_edgeSet : vertexCoverNum G ≤ G.edgeSet.encard := by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  have := ne_bot_iff_exists_adj.mp (by simpa using h')
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff, Subtype.forall] at hn
  have := hn ((·.out.1) '' G.edgeSet) (fun v w hadj ↦ by
    have := Sym2.mem_iff.mp <| Sym2.out_fst_mem s(v, w)
    grind [mem_edgeSet])
  grw [this]
  exact Set.encard_image_le (fun x ↦ (Quot.out x).1) G.edgeSet

@[simp]
theorem vertexCoverNum_ne_top_of_edgeSet_finite (h : G.edgeSet.Finite) : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) (@vertexCoverNum_le_encard_edgeSet V G)

theorem vertexCoverNum_top : vertexCoverNum (completeGraph V) = ENat.card V - 1 := by
  by_cases h' : Subsingleton V
  · simp [tsub_eq_zero_of_le]
  rw [not_subsingleton_iff_nontrivial] at h'
  obtain ⟨x⟩ := h'.to_nonempty
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  · by_contra! hh
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

theorem vertexCoverNum_le_of_relHom (f : G →g H) (hf : Function.Injective f) :
    vertexCoverNum G ≤ vertexCoverNum H := by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
  have := H.isIndepSet_iff_isAntichain_adj.mp <| isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj ↦ f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
    isIndepSet_compl_iff_isVertexCover.mp <| G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
  exact Function.Embedding.encard_le <| Function.Embedding.mk f hf |>.subtypeMap (by simp)

theorem vertexCoverNum_eq_of_relIso (f : G ≃g H) : vertexCoverNum G = vertexCoverNum H :=
  le_antisymm (vertexCoverNum_le_of_relHom f.toHom f.injective)
    (vertexCoverNum_le_of_relHom f.symm.toHom f.symm.injective)

end vertexCoverNum
end SimpleGraph
