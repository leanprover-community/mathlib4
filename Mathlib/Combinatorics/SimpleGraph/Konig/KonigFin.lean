/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Konig.Auxillary
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic


open Cardinal Finset SimpleGraph

namespace SimpleGraph
namespace Konig

/-!
# Kőnig’s theorem: finite variation

This file proves Kőnig’s theorem for *finite* bipartite simple graphs:
the size of a maximum matching equals the size of a minimum vertex cover.

The argument uses the finite Hall marriage theorem to construct, from a minimum
vertex cover `C`, two disjoint matchings saturating `s ∩ C` and `t ∩ C`. Their
union is a matching of size `#C`.

## Main statement

* `konig_fin`: for finite bipartite `G`, any minimum vertex cover `C` and any
  maximum matching `M` satisfy `#M.edgeSet = #C`.

## Tags
Kőnig, matching, vertex cover, bipartite, Hall
-/

variable {V : Type*}
{G : SimpleGraph V} {s t : Set V} {hbi : G.IsBipartiteWith s t}
variable {C : Set V} {M : Subgraph G} (hM : M.IsMatching)

lemma disjoint_inter_union_sdiff {s t u : Set V} (h : Disjoint s t) :
    Disjoint (s ∩ u ∪ t \ u) (t ∩ u ∪ s \ u) := by
  simp only [Set.disjoint_union_right, Set.disjoint_union_left]
  and_intros <;> try (
    refine Set.disjoint_of_subset (s₂ := s) (t₂ := t) ?_ ?_ ?_ <;>
    solve | exact disj_st | exact Set.inter_subset_left (t := u) | exact h
  )
  · exact Set.disjoint_sdiff_inter
  · symm; exact Set.disjoint_sdiff_inter
  · exact Set.disjoint_of_subset Set.diff_subset Set.diff_subset h.symm

variable [Fintype V]

lemma hall_condition {hbi : G.IsBipartiteWith s t} (hminC : G.IsMinSizeCover C)
    : ∀ A : Finset ↑(s ∩ C), A.card ≤ #{v | v ∈ t \ C ∧ ∃ w : A, G.Adj v w} := by
  intro A
  let A_set: Set ↑(s ∩ C) := SetLike.coe A
  set B : Set V := {v | v ∈ t \ C ∧ ∃ w : A, G.Adj v w}
  let C' := (C \ A_set) ∪ B
  have hdisj := hbi.disjoint
  have hAsubC : (A_set : Set V) ⊆ C := by (rintro _ ⟨⟨v, hvC⟩, hv⟩; simp_all; exact hv.2 ▸ hvC.2)
  have disj : Disjoint (A_set : Set V) (C \ A_set : Set V) := Set.disjoint_sdiff_right
  by_contra! hcard
  have hcardlt : #↑C' < #↑C := calc
    #C' ≤  #(C \ A_set : Set V) + #↑B := mk_union_le (C \ A_set : Set V) B
    _ = #↑B + #(C \ A_set : Set V) := add_comm _ #B
    _ < #A_set + #(C \ A_set : Set V) :=
      (add_lt_add_iff_of_lt_aleph0 mk_lt_aleph0).mpr (by simpa [A_set])
    _ =(↑#(Subtype.val '' ↑A)) + #(C \ A_set : Set V) := by
      refine congr_arg (· + #(C \ A_set : Set V)) ?_
      exact (Cardinal.mk_image_eq (Subtype.val_injective)).symm
    _ = #↑((A_set : Set V) ∪ C \ A_set) := (mk_union_of_disjoint disj).symm
    _ = #C := congr_arg (fun x : Set V => #x) (by simpa using hAsubC)
  refine not_le.mpr hcardlt (hminC.right C' ?_)
  dsimp only [SimpleGraph.IsVertexCover];
  intro v w hadj
  by_contra!; obtain ⟨hnv, hnw⟩ := this
  have : v ∉ C ∨ w ∉ C := by
    by_contra! h'; obtain ⟨hvC, hwC⟩ := h'
    rcases hbi.mem_of_adj hadj with (⟨_, hut⟩ | ⟨hut, _⟩) <;>
    all_goals (simp_all [C', B]; refine (Set.disjoint_left.mp hdisj) ?_ hut)
    · obtain ⟨hus, h⟩ := hnw; assumption
    · obtain ⟨hus, h⟩ := hnv; assumption
  have hvw : v ∈ C ∨ w ∈ C := hminC.left hadj
  rcases hvw with hvC | hwC
  · suffices hwB : w ∈ B from absurd (Or.inr hwB) hnw
    simp [hvC, C', B] at hnv
    simp [B, -exists_and_right]
    obtain ⟨hvs, _⟩ := hnv
    let v_A : ↑(s ∩ C) := ⟨v, ⟨hvs, hvC⟩⟩
    refine And.intro ?_ ?_
    · exact ⟨hbi.mem_of_mem_adj hvs hadj, by simp_all⟩
    · exact ⟨v_A, ⟨v_A.prop, ⟨by simpa, G.adj_symm hadj⟩⟩⟩
  · suffices hvB : v ∈ B from absurd (Or.inr hvB) hnv
    simp [hwC, C', B] at hnw
    simp [B, -exists_and_right]
    obtain ⟨hws, hwa⟩ := hnw
    constructor
    · simp_all; exact hbi.mem_of_mem_adj hws hadj.symm
    · refine ⟨w, ⟨⟨hws, hwC⟩, ⟨?_, hadj⟩⟩⟩;simpa

lemma hall_wrapper (hbi : G.IsBipartiteWith s t) (hminC : G.IsMinSizeCover C)
    : ∃ f : ↑(s ∩ C) → V, Function.Injective f ∧ ∀ v : ↑(s ∩ C), G.Adj v (f v) ∧ f v ∈ t \ C :=
    by classical
  let s' := (s ∩ C)
  have hall_cond := hall_condition (hbi := hbi) hminC
  let τ : s' → Finset V := fun v => {w : V | G.Adj v w ∧ w ∈ t \ C}
  suffices ht : ∀ A : Finset s', (#A : ℕ) ≤ (#(A.biUnion τ) : ℕ) from by
    obtain ⟨f, f_inf, hf⟩ := HallMarriageTheorem.hall_hard_inductive ht
    refine ⟨f, ⟨f_inf, ?_⟩⟩
    intro v
    simpa [τ] using hf v
  intro A
  suffices h : {v : V | v ∈ t \ C ∧ ∃ w : A, G.Adj v w} = A.biUnion τ from by
    set B := A.biUnion τ with hB
    have res := h ▸ hall_cond A
    simpa using res
  ext v
  simp [τ]
  apply Iff.intro
  · rintro ⟨hv, ⟨w, ⟨hw, hadj⟩⟩⟩
    exact ⟨w, ⟨hadj.symm, ⟨hv.left, ⟨hw, hv.right⟩⟩⟩⟩
  · rintro ⟨v, ⟨hadj, ⟨hwt, ⟨⟨hvs', hva⟩, hwnC⟩⟩⟩⟩
    exact ⟨⟨hwt, hwnC⟩, ⟨v, ⟨⟨hvs', hva⟩, hadj.symm⟩⟩⟩

lemma hard_side_finite_graph
    (hbi : G.IsBipartiteWith s t) (hmin : G.IsMinSizeCover C)
    : ∃ M : Subgraph G, M.IsMatching ∧ #M.edgeSet = #C := by
  let s' : Set V := s ∩ C
  let t' : Set V := t ∩ C
  have hdisj_st' : Disjoint s' t' :=
    Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left hbi.disjoint
  have : C.Finite := Set.Finite.subset Set.finite_univ <| Set.subset_univ C
  have hCminimal := finite_min_size_cover_minimal hmin this
  have huni : C ⊆ s ∪ t := by
    intro v hvc
    obtain ⟨w, hadj⟩ := (minimal_cover_no_isolated hCminimal) v hvc
    rcases hbi.mem_of_adj hadj with h | h <;> simp_all only [Set.mem_union, true_or, or_true]
  obtain ⟨f, f_inj, hf⟩ := hall_wrapper hbi hmin
  have f_range : ↑(Set.range f) ⊆ t \ C := by (rintro v ⟨w, hwv⟩; exact hwv ▸ (hf w).right)
  have hdisj_s'f : Disjoint s' ↑(Set.range f) :=
    (Set.disjoint_of_subset Set.inter_subset_left (f_range.trans Set.diff_subset) hbi.disjoint)
  obtain ⟨M₀, vert₀, hM₀⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    hdisj_s'f (Equiv.ofInjective f f_inj) (forall_and.mp hf).left
  obtain ⟨g, g_inj, hg⟩ := hall_wrapper hbi.symm hmin
  have g_range : ↑(Set.range g) ⊆ s \ C := by (rintro v ⟨w, hwv⟩; exact hwv ▸ (hg w).right)
  have hdisj_t'g : Disjoint t' ↑(Set.range g) :=
    (Set.disjoint_of_subset Set.inter_subset_left (g_range.trans Set.diff_subset) hbi.disjoint.symm)
  obtain ⟨M₁, vert₁, hM₁⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    hdisj_t'g (Equiv.ofInjective g g_inj) (forall_and.mp hg).left
  let M := M₀ ⊔ M₁
  use M
  have hdisj_verts : Disjoint M₀.verts M₁.verts := by
    rw [vert₀, vert₁]
    refine Set.disjoint_of_subset (s₂ := s' ∪ t \ C) (t₂ := t' ∪ s \ C) ?S ?T ?_ <;>
    try (apply Set.union_subset_union_right _ <;> assumption)
    simpa [s', t'] using disjoint_inter_union_sdiff hbi.disjoint
  have hdisj : Disjoint M₀ M₁ := Subgraph.disjoint_iff_disjoint_verts.mp hdisj_verts
  have card₀ : #M₀.edgeSet = #s' := by
    refine mul_left_cancel_of_nat (hneq0 := two_ne_zero)
      <| hM₀.edge_card_eq_double_vert_card  ▸ vert₀ ▸ ?_
    exact (mk_union_of_disjoint hdisj_s'f).trans ((mk_range_eq f f_inj).symm ▸ (two_mul #s').symm)
  have card₁ : #M₁.edgeSet = #t' := by
    refine mul_left_cancel_of_nat (hneq0 := two_ne_zero)
       <| hM₁.edge_card_eq_double_vert_card  ▸ vert₁ ▸ ?_
    exact (mk_union_of_disjoint hdisj_t'g).trans ((mk_range_eq g g_inj).symm ▸ (two_mul #t').symm)
  constructor
  · refine Subgraph.IsMatching.sup hM₀ hM₁ ?_
    simp_all only [Subtype.forall, Subgraph.IsMatching.support_eq_verts]
  · have : M.edgeSet = M₀.edgeSet ∪ M₁.edgeSet := by simp [M]
    calc
    #M.edgeSet
    _ = #↑M₀.edgeSet + #↑M₁.edgeSet := this ▸ (mk_union_of_disjoint <| Disjoint.edgeSet hdisj)
    _ = #↑s' + #↑t' := by simp only [card₀, card₁]
    _ = #↑(s' ∪ t') := by simp only [mk_union_of_disjoint hdisj_st']
    _ = #↑((s ∪ t) ∩ C) := by simp only [Set.union_inter_distrib_right, s', t']
    _ = #↑C := by simp [Set.inter_eq_self_of_subset_right huni]

theorem konig_fin
    (hbi : G.IsBipartiteWith s t) (hminC : G.IsMinSizeCover C) (hmaxM : M.IsMaxSizeMatching) :
    #M.edgeSet = #C := by classical
  have hle : #↑M.edgeSet ≤ #↑C := konig_easy_side hminC.left hmaxM.left
  have ⟨M₀, ⟨hM₀, hcard₀⟩⟩ := hard_side_finite_graph hbi hminC
  exact le_antisymm hle <| hcard₀ ▸ hmaxM.right M₀ hM₀

end Konig
end SimpleGraph
