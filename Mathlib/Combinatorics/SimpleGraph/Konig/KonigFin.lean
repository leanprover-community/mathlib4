/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Konig.Auxillary
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Kőnig’s theorem: finite variation

This file proves Kőnig’s theorem for *finite* bipartite simple graphs:
the size of a maximum matching equals the size of a minimum vertex cover.

The argument uses the finite Hall marriage theorem to construct, from a minimum
vertex cover `C`, two disjoint matchings saturating `s ∩ C` and `t ∩ C`. Their
union is a matching of size `#C`.

## Main statement

* `konig_bipartite_fin`: for finite bipartite `G`, any minimum vertex cover `C` and any
  maximum matching `M` satisfy `#M.edgeSet = #C`.

## Tags
Kőnig, matching, vertex cover, bipartite, Hall
-/

open Cardinal Finset SimpleGraph Set

namespace SimpleGraph
namespace Konig

variable {V : Type*}
{G : SimpleGraph V} {s t : Set V} {hbi : G.IsBipartiteWith s t}
variable {C : Set V} {M : Subgraph G} (hM : M.IsMatching)

def IsMinimalCover (G : SimpleGraph V) (C : Set V) :=
   G.IsVertexCover C ∧ ∀ C' ≤ C, G.IsVertexCover C' → C' = C

def IsMinSizeCover (G : SimpleGraph V) (C : Set V) :=
   G.IsVertexCover C ∧ ∀ (C' : Set V), G.IsVertexCover C' → #C' ≥ #C

lemma finite_min_size_cover_minimal (hmin : IsMinSizeCover G C) (hfinC : C.Finite) :
     IsMinimalCover G C := by
  refine ⟨hmin.left, fun C' hle hC' => Finite.eq_of_subset_of_card_le hfinC hle ?_⟩
  have hcardle : #C ≤ #C' := hmin.right C' hC'
  have hfinC' := (Finite.subset hfinC hle)
  suffices h : Nat.card C = #C ∧ Nat.card C' = #↑C' from by
    exact_mod_cast (by simpa [h.1.symm, h.2.symm] using hcardle)
  constructor <;>
  exact Cardinal.cast_toNat_of_lt_aleph0 <| Cardinal.lt_aleph0_iff_finite.mpr (by assumption)


lemma minimal_cover_no_isolated (hminc : IsMinimalCover G C) : ∀ v ∈ C, ∃ w, G.Adj v w := by
  by_contra! hcontra
  obtain ⟨v, ⟨hvc, hnadj⟩⟩ := hcontra
  let C' : Set V := C \ {v}
  have hneq : C' ≠ C := fun h => by simp_all [C']
  suffices h : IsVertexCover G C' from (absurd · hneq) <| hminc.right C' diff_subset h
  intro w₁ w₂ hadj
  have hwᵢC : w₁ ∈ C ∨ w₂ ∈ C := hminc.left hadj
  rcases hwᵢC with hwᵢC | hwᵢC
  · refine Or.inl ⟨hwᵢC, ?_⟩; by_contra! hwv; exact absurd (hwv ▸ hadj) (hnadj w₂)
  · refine Or.inr ⟨hwᵢC, ?_⟩; by_contra! hwv; exact absurd (hwv ▸ hadj).symm (hnadj w₁)

private lemma disjoint_inter_union_sdiff {s t u : Set V} (h : Disjoint s t) :
    Disjoint (s ∩ u ∪ t \ u) (t ∩ u ∪ s \ u) := by grind

variable [Fintype V]

lemma hall_condition {hbi : G.IsBipartiteWith s t} (hminC : IsMinSizeCover G C)
    : ∀ A : Finset ↑(s ∩ C), A.card ≤ #{v | v ∈ t \ C ∧ ∃ w : A, G.Adj v w} :=by
  intro A
  let A_set: Set ↑(s ∩ C) := SetLike.coe A
  set B : Set V := {v | v ∈ t \ C ∧ ∃ w : A, G.Adj v w}
  let C' := (C \ A_set) ∪ B
  have hdisj := hbi.disjoint
  have hAsubC : (A_set : Set V) ⊆ C := by grind
  have disj : Disjoint (A_set : Set V) (C \ A_set : Set V) := disjoint_sdiff_right
  suffices hc'cover : IsVertexCover G C' from by
    by_contra! hcard
    refine not_le.mpr ?_ (hminC.right C' hc'cover)
    exact by calc
    #C' ≤  #(C \ A_set : Set V) + #↑B := mk_union_le (C \ A_set : Set V) B
    _ = #↑B + #(C \ A_set : Set V) := add_comm _ #B
    _ < #A_set + #(C \ A_set : Set V) :=
      (add_lt_add_iff_of_lt_aleph0 mk_lt_aleph0).mpr (by simpa [A_set])
    _ =(↑#(Subtype.val '' ↑A)) + #(C \ A_set : Set V) := by
      refine congr_arg (· + #(C \ A_set : Set V)) ?_
      exact (Cardinal.mk_image_eq (Subtype.val_injective)).symm
    _ = #↑((A_set : Set V) ∪ C \ A_set) := (mk_union_of_disjoint disj).symm
    _ = #C := congr_arg (fun x : Set V => #x) (by simpa using hAsubC)
  suffices h : ∀ {v w : V}, G.Adj v w → v ∈ C → v ∈ C' ∨ w ∈ C' from by
    intro v w hadj
    rcases hminC.left hadj with hvC | hwC
    · exact h hadj hvC
    · exact (h hadj.symm hwC).symm
  intro v w hadj hvC
  by_contra!; obtain ⟨hnv, hnw⟩ := this
  suffices hwB : w ∈ B from absurd (Or.inr hwB) hnw
  have hvs : v ∈ s := by grind
  have hwt : w ∈ t := hbi.mem_of_mem_adj hvs hadj
  exact ⟨⟨hwt, by grind⟩, ⟨⟨⟨v, ⟨hvs, hvC⟩⟩, by grind⟩, hadj.symm⟩⟩

lemma hall_wrapper (hbi : G.IsBipartiteWith s t) (hminC : IsMinSizeCover G C)
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
  constructor <;>
  (simp only [mem_diff, coe_biUnion, SetLike.mem_coe, coe_filter, iUnion_coe_set,
   mem_iUnion, mem_setOf_eq, exists_and_left, exists_prop, exists_and_right, Subtype.exists,
   forall_exists_index, and_imp, τ]
   intros
   symm_saturate
   grind)

public lemma konig_finite_graph
    (hbi : G.IsBipartiteWith s t) (hmin : IsMinSizeCover G C)
    : ∃ M : Subgraph G, M.IsMatching ∧ #M.edgeSet = #C := by
  let s' : Set V := s ∩ C
  let t' : Set V := t ∩ C
  have hdisj_st' : Disjoint s' t' :=
    disjoint_of_subset inter_subset_left inter_subset_left hbi.disjoint
  have : C.Finite := Finite.subset finite_univ <| subset_univ C
  have hCminimal := finite_min_size_cover_minimal hmin this
  have huni : C ⊆ s ∪ t := by
    intro v hvc
    obtain ⟨w, hadj⟩ := (minimal_cover_no_isolated hCminimal) v hvc
    rcases hbi.mem_of_adj hadj with h | h <;> simp_all only [mem_union, true_or, or_true]
  obtain ⟨f, f_inj, hf⟩ := hall_wrapper hbi hmin
  have f_range : ↑(range f) ⊆ t \ C := by (rintro v ⟨w, hwv⟩; exact hwv ▸ (hf w).right)
  have hdisj_s'f : Disjoint s' ↑(range f) :=
    (disjoint_of_subset inter_subset_left (f_range.trans diff_subset) hbi.disjoint)
  obtain ⟨M₀, vert₀, hM₀⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    hdisj_s'f (Equiv.ofInjective f f_inj) (forall_and.mp hf).left
  obtain ⟨g, g_inj, hg⟩ := hall_wrapper hbi.symm hmin
  have g_range : ↑(range g) ⊆ s \ C := by (rintro v ⟨w, hwv⟩; exact hwv ▸ (hg w).right)
  have hdisj_t'g : Disjoint t' ↑(range g) :=
    (disjoint_of_subset inter_subset_left (g_range.trans diff_subset) hbi.disjoint.symm)
  obtain ⟨M₁, vert₁, hM₁⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    hdisj_t'g (Equiv.ofInjective g g_inj) (forall_and.mp hg).left
  let M := M₀ ⊔ M₁
  use M
  have hdisj_verts : Disjoint M₀.verts M₁.verts := by
    rw [vert₀, vert₁]
    refine disjoint_of_subset (s₂ := s' ∪ t \ C) (t₂ := t' ∪ s \ C) ?S ?T ?_ <;>
    try (apply union_subset_union_right _ <;> assumption)
    simpa [s', t'] using disjoint_inter_union_sdiff hbi.disjoint
  have hdisj : Disjoint M₀ M₁ := SimpleGraph.Subgraph.disjoint_verts_iff_disjoint.mp hdisj_verts
  have card₀ : #M₀.edgeSet = #s' := by
     refine (nat_mul_cancel_iff two_ne_zero).mp <| hM₀.edge_card_eq_double_vert_card.symm.trans ?_
     simp [s', vert₀, mk_union_of_disjoint hdisj_s'f, mk_range_eq f f_inj, two_mul #s']
  have card₁ : #M₁.edgeSet = #t' := by
     refine (nat_mul_cancel_iff two_ne_zero).mp <| hM₁.edge_card_eq_double_vert_card.symm.trans ?_
     simp [t', vert₁, mk_union_of_disjoint hdisj_t'g, mk_range_eq g g_inj, two_mul #t']
  constructor
  · refine Subgraph.IsMatching.sup hM₀ hM₁ ?_
    simp_all [Subtype.forall, Subgraph.IsMatching.support_eq_verts]
  · have : M.edgeSet = M₀.edgeSet ∪ M₁.edgeSet := by simp [M]
    calc
    #M.edgeSet
    _ = #↑M₀.edgeSet + #↑M₁.edgeSet := this ▸ (mk_union_of_disjoint <| Disjoint.edgeSet hdisj)
    _ = #↑s' + #↑t' := by simp [card₀, card₁]
    _ = #↑(s' ∪ t') := by simp [mk_union_of_disjoint hdisj_st']
    _ = #↑((s ∪ t) ∩ C) := by simp [union_inter_distrib_right, s', t']
    _ = #↑C := by simp [inter_eq_self_of_subset_right huni]

public theorem konig_bipartite_fin
    (hbi : G.IsBipartiteWith s t) (hminC : IsMinSizeCover G C) (hmaxM : M.IsMaxSizeMatching) :
    #M.edgeSet = #C := by
  have hle : #↑M.edgeSet ≤ #↑C := konig_card_matching_le_card_cover hminC.left hmaxM.left
  have ⟨M₀, ⟨hM₀, hcard₀⟩⟩ := konig_finite_graph hbi hminC
  exact hle.antisymm <| hcard₀ ▸ hmaxM.right hM₀ (by simpa [hcard₀])

end Konig
end SimpleGraph
