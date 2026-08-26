/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VizingTheorem.Basic

@[expose] public section

variable (n : ℕ) [Fact (0 < n)]
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableEq (Fin n)]
  [Nonempty (Fin n)]

/-- **Upper bound by induction on the number of edges.**
    For every simple graph `H`, the chromatic index satisfies
    `χ'(H) ≤ Δ(H) + 1`. -/
private lemma vizingUpperBound_aux : ∀ (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    [DecidableRel H.Adj], H.edgeFinset.card ≤ k →
    vizing.chromaticIndex H ≤ H.maxDegree + 1 := by
  intro k
  induction k with
  | zero =>
    intro m H _ h
    have h_card : Fintype.card H.edgeSet = 0 := by
      rw [← H.edgeFinset_card]; exact Nat.le_zero.mp h
    haveI : IsEmpty H.edgeSet := Fintype.card_eq_zero_iff.mp h_card
    unfold vizing.chromaticIndex
    rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]; simp
  | succ k ih =>
    intro m H _ h
    by_cases h_empty : H.edgeFinset.card = 0
    · have h_card : Fintype.card H.edgeSet = 0 := by
        rw [← H.edgeFinset_card]; exact h_empty
      haveI : IsEmpty H.edgeSet := Fintype.card_eq_zero_iff.mp h_card
      unfold vizing.chromaticIndex
      rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]; simp
    · -- At least one edge: remove it and apply the induction hypothesis.
      push Not at h_empty
      obtain ⟨e_sym, he_mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h_empty)
      have he_mem' : e_sym ∈ H.edgeSet := (H.mem_edgeFinset).mp he_mem
      let e : H.edgeSet := ⟨e_sym, he_mem'⟩
      obtain ⟨u, v, huv⟩ : ∃ u v : Fin m, e.val = s(u, v) :=
        e.val.ind (fun a b => ⟨a, b, rfl⟩)
      have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
      haveI : Fact (0 < m) := ⟨hm_pos⟩
      haveI : Nonempty (Fin m) := ⟨u⟩
      have h_H'_card : (H.deleteEdges {e.val}).edgeFinset.card ≤ k := by
        have h_eq : (H.deleteEdges {e.val}).edgeFinset = H.edgeFinset.erase e_sym := by
          ext f
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
                     Finset.mem_erase, Set.mem_sdiff, Set.mem_singleton_iff]
          tauto
        rw [h_eq, Finset.card_erase_of_mem he_mem]; omega
      have h_Δ : (H.deleteEdges {e.val}).maxDegree ≤ H.maxDegree := by
        apply SimpleGraph.maxDegree_le_of_forall_degree_le
        intro w
        exact (SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)).trans
          (H.degree_le_maxDegree w)
      have h_H'_bound :
          vizing.chromaticIndex (H.deleteEdges {e.val}) ≤ H.maxDegree + 1 :=
        calc vizing.chromaticIndex (H.deleteEdges {e.val})
            ≤ (H.deleteEdges {e.val}).maxDegree + 1 := ih (H.deleteEdges {e.val}) h_H'_card
          _ ≤ H.maxDegree + 1 := by omega
      -- Extract a witness coloring of H' with Δ+1 colors.
      have h_c'_nonempty :
          Nonempty ((H.deleteEdges {e.val}).lineGraph.Coloring (Fin (H.maxDegree + 1))) := by
        have h_toNat_le :=  h_H'_bound
        have h_col_fin := SimpleGraph.colorable_of_fintype (H.deleteEdges {e.val}).lineGraph
        have h_chi_le_card := h_col_fin.chromaticNumber_le
        have h_chi_ne_top :
            (H.deleteEdges {e.val}).lineGraph.chromaticNumber ≠ ⊤ := by
          intro heq; rw [heq, top_le_iff] at h_chi_le_card
          exact ENat.coe_ne_top _ h_chi_le_card
        have h_chi_le :
            (H.deleteEdges {e.val}).lineGraph.chromaticNumber ≤
              ((H.maxDegree + 1 : ℕ) : ℕ∞) := by
          rw [← ENat.coe_toNat h_chi_ne_top]; exact_mod_cast h_toNat_le
        exact SimpleGraph.chromaticNumber_le_iff_colorable.mp h_chi_le
      let c' := h_c'_nonempty.some
      -- Case-split: is some color free at both u and v?
      have h_case :
          (∃ color : Fin (H.maxDegree + 1),
            (∀ e' : (H.deleteEdges {e.val}).edgeSet, u ∈ e'.val → c'.toFun e' ≠ color) ∧
            (∀ e' : (H.deleteEdges {e.val}).edgeSet, v ∈ e'.val → c'.toFun e' ≠ color))
          ∨
          (∀ color : Fin (H.maxDegree + 1),
            (∃ e₁ : (H.deleteEdges {e.val}).edgeSet, u ∈ e₁.val ∧ c'.toFun e₁ = color) ∨
            (∃ e₂ : (H.deleteEdges {e.val}).edgeSet, v ∈ e₂.val ∧ c'.toFun e₂ = color)) := by
        by_cases h : ∃ color : Fin (H.maxDegree + 1),
            (∀ e' : (H.deleteEdges {e.val}).edgeSet, u ∈ e'.val → c'.toFun e' ≠ color) ∧
            (∀ e' : (H.deleteEdges {e.val}).edgeSet, v ∈ e'.val → c'.toFun e' ≠ color)
        · exact Or.inl h
        · right; intro color
          by_cases h_u : ∃ e₁ : (H.deleteEdges {e.val}).edgeSet,
              u ∈ e₁.val ∧ c'.toFun e₁ = color
          · exact Or.inl h_u
          · right; push Not at h h_u; exact h color h_u
      cases h_case with
      | inl h_color_free =>
        -- Case A: free color at both endpoints — extend directly.
        obtain ⟨color, h_free_u, h_free_v⟩ := h_color_free
        obtain ⟨c, _⟩ :=
          extendColoringOneEdge m H e huv c' color h_free_u h_free_v
        have h_col : H.lineGraph.Colorable (H.maxDegree + 1) := ⟨c⟩
        change H.lineGraph.chromaticNumber.toNat ≤ H.maxDegree + 1
        exact ENat.toNat_le_of_le_coe h_col.chromaticNumber_le
      | inr _h_no_free_color =>
        -- Case B: use the Vizing adjacency lemma.
        have h_deg_u_lt : (H.deleteEdges {e.val}).degree u < H.maxDegree + 1 := by
          have h1 : (H.deleteEdges {e.val}).degree u ≤ H.degree u :=
            SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)
          have h2 : H.degree u ≤ H.maxDegree := H.degree_le_maxDegree u
          omega
        have h_deg_v_lt : (H.deleteEdges {e.val}).degree v < H.maxDegree + 1 := by
          have h1 : (H.deleteEdges {e.val}).degree v ≤ H.degree v :=
            SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le _)
          have h2 : H.degree v ≤ H.maxDegree := H.degree_le_maxDegree v
          omega
        have h_missing_u : (vizing.missingColors c' u).Nonempty :=
          vizing.missingColors_nonempty_of_degree_lt c' u
            (by rw [Fintype.card_fin]; exact h_deg_u_lt)
        have h_missing_v : (vizing.missingColors c' v).Nonempty :=
          vizing.missingColors_nonempty_of_degree_lt c' v
            (by rw [Fintype.card_fin]; exact h_deg_v_lt)
        have h_card : H.maxDegree < Fintype.card (Fin (H.maxDegree + 1)) := by
          rw [Fintype.card_fin]; omega
        have h_missing_u_card :
            2 ≤ (vizing.missingColors c' u).ncard := by
          classical
          have h_u_in_e : u ∈ e_sym := by
            change u ∈ e.val; rw [huv]; exact Sym2.mem_mk_left u v
          have h_e_in_inc : e_sym ∈ H.incidenceFinset u := by
            rw [SimpleGraph.mem_incidenceFinset]; exact ⟨he_mem', h_u_in_e⟩
          have h_erase :
              (H.deleteEdges {e.val}).incidenceFinset u =
                (H.incidenceFinset u).erase e_sym := by
            ext f
            simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
                       SimpleGraph.edgeSet_deleteEdges, Set.mem_setOf_eq,
                       Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase]
            tauto
          have h_card_eq :
              (H.deleteEdges {e.val}).degree u + 1 = H.degree u := by
            rw [← SimpleGraph.card_incidenceFinset_eq_degree,
                ← SimpleGraph.card_incidenceFinset_eq_degree, h_erase,
                Finset.card_erase_of_mem h_e_in_inc]
            have h_card_pos : 0 < (H.incidenceFinset u).card :=
              Finset.card_pos.mpr ⟨e_sym, h_e_in_inc⟩
            omega
          apply vizing.missingColors_ncard_ge_two c' u
          rw [Fintype.card_fin]
          have h_max : H.degree u ≤ H.maxDegree := H.degree_le_maxDegree u
          omega
        obtain ⟨c_full⟩ :=
          vizing.vizingAdjacencyLemma e huv c' h_missing_u h_missing_v h_card
            h_missing_u_card
        have h_col : H.lineGraph.Colorable (H.maxDegree + 1) := ⟨c_full⟩
        change H.lineGraph.chromaticNumber.toNat ≤ H.maxDegree + 1
        exact ENat.toNat_le_of_le_coe h_col.chromaticNumber_le

omit [Fact (0 < n)] [DecidableEq (Fin n)] in
/-- **Vizing's theorem**: the chromatic index of a simple graph equals either
    its maximum degree Δ or Δ + 1. -/
theorem vizingTheorem :
    (vizing.chromaticIndex G = G.maxDegree) ∨ (vizing.chromaticIndex G = G.maxDegree + 1) := by
  have h_lower : vizing.chromaticIndex G ≥ G.maxDegree :=
    maxDegree_le_chromaticIndex n G
  have h_upper : vizing.chromaticIndex G ≤ G.maxDegree + 1 :=
    vizingUpperBound_aux G.edgeFinset.card G (le_refl _)
  omega
