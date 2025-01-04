/-
Copyright (c) 2024 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The Kővári–Sós–Turán theorem

This modules proves the **Kővári–Sós–Turán theorem** for simple graphs.

## Main definitions

* `SimpleGraph.completeBipartiteGraph_isIsoSubgraph_iff` is the proof of an equivalence for simple
  graphs containing a copy of `completeBipartiteGraph α β`.

* `SimpleGraph.card_edgeFinset_le_of_completeBipartiteGraph_free` is the proof of the
  **Kővári–Sós–Turán theorem** for simple graphs.

* `SimpleGraph.extremalNumber_completeBipartiteGraph_le` is the proof of the corollary of the
  **Kővári–Sós–Turán theorem** upper bounding the extremal numbers of `completeBipartiteGraph α β`.
-/


open Fintype

namespace SimpleGraph

variable {V α β : Type*} [Fintype V] [Fintype α] [Fintype β]

/-- `G` contains a copy of `completeBipartiteGraph α β` iff there exist a set of `card α` vertices
adjacent to a set of `card β` vertices in `G`. -/
theorem completeBipartiteGraph_isIsoSubgraph_iff {G : SimpleGraph V} :
    (completeBipartiteGraph α β).IsIsoSubgraph G
      ↔ ∃ (A : Finset.univ.powersetCard (card α))
          (B : Finset.univ.powersetCard (card β)),
          ∀ v₁ ∈ A.val, ∀ v₂ ∈ B.val, G.Adj v₁ v₂ := by
  constructor
  · intro ⟨f⟩
    let A := Finset.univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩
    have hA : A ∈ Finset.univ.powersetCard (card α) := by
      rw [Finset.mem_powersetCard_univ, Finset.card_map, Finset.card_univ]
    use ⟨A, hA⟩
    let B := Finset.univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩
    have hB : B ∈ Finset.univ.powersetCard (card β) := by
      rw [Finset.mem_powersetCard_univ, Finset.card_map, Finset.card_univ]
    use ⟨B, hB⟩
    intro v₁ hv₁ v₂ hv₂
    rw [Finset.mem_map] at hv₁ hv₂
    obtain ⟨a, _, ha⟩ := hv₁
    obtain ⟨b, _, hb⟩ := hv₂
    rw [←ha, ←hb]
    exact f.toHom.map_adj (by simp)
  · intro ⟨⟨A, hA⟩, ⟨B, hB⟩, h⟩
    rw [Finset.mem_powersetCard_univ] at hA hB
    haveI : Nonempty (α ↪ A) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [card_coe]
      exact ge_of_eq hA
    let fa : α ↪ A := Classical.arbitrary (α ↪ A)
    haveI : Nonempty (β ↪ B) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [card_coe]
      exact ge_of_eq hB
    let fb : β ↪ B := Classical.arbitrary (β ↪ B)
    let f : α ⊕ β ↪ V := by
      use Sum.elim (Subtype.val ∘ fa) (Subtype.val ∘ fb)
      intro ab₁ ab₂
      match ab₁, ab₂ with
      | Sum.inl a₁, Sum.inl a₂ =>
        simp [←Subtype.ext_iff]
      | Sum.inr b₁, Sum.inl a₂ =>
        have hadj := h (fa a₂) (fa a₂).prop (fb b₁) (fb b₁).prop
        simp [hadj.ne']
      | Sum.inl a₁, Sum.inr b₂ =>
        have hadj := h (fa a₁) (fa a₁).prop (fb b₂) (fb b₂).prop
        simp [hadj.symm.ne']
      | Sum.inr b₁, Sum.inr b₂ =>
        simp [←Subtype.ext_iff]
    use ⟨f.toFun, ?_⟩, f.injective
    intro ab₁ ab₂ hadj
    rcases hadj with ⟨hab₁, hab₂⟩ | ⟨hab₁, hab₂⟩
    all_goals dsimp [f]
    · rw [←Sum.inl_getLeft ab₁ hab₁, ←Sum.inr_getRight ab₂ hab₂,
        Sum.elim_inl, Sum.elim_inr]
      exact h (fa _) (by simp) (fb _) (by simp)
    · rw [←Sum.inr_getRight ab₁ hab₁, ←Sum.inl_getLeft ab₂ hab₂,
        Sum.elim_inl, Sum.elim_inr, adj_comm]
      exact h (fa _) (by simp) (fb _) (by simp)

variable [DecidableEq V]

section KovariSosTuran

/-- This is an auxiliary definition for the double-counting argument in the proof of the
Kővári–Sós–Turán theorem. -/
private abbrev aux (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :=
  (Finset.univ.powersetCard n ×ˢ Finset.univ).filter fun (t, v) ↦ t ⊆ G.neighborFinset v

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- This is an auxiliary lemma for the double-counting argument in the proof of the
Kővári–Sós–Turán theorem, counting over subsets. -/
private lemma card_aux_le
    [Nonempty β] (h : (completeBipartiteGraph α β).Free G) :
    (aux G (card α)).card
      ≤ (((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ) := by
  trans ((card V).choose (card α))*(card β-1)
  · simp_rw [Finset.card_filter _, Finset.sum_product, ←Finset.card_filter, ←@Finset.card_univ V,
      ←Finset.card_powersetCard, ←nsmul_eq_mul, ←Finset.sum_const, ←Nat.cast_pred card_pos,
      ←Nat.cast_sum, Nat.cast_le]
    apply Finset.sum_le_sum
    intro t ht_mem
    contrapose! h
    have ⟨t', ht'⟩ := Finset.exists_subset_card_eq h
    rw [←Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at ht'
    have ht'_mem : t' ∈ Finset.univ.powersetCard (card β) := by
      rw [Finset.mem_powersetCard_univ]
      exact ht'.2
    rw [not_not, completeBipartiteGraph_isIsoSubgraph_iff]
    use ⟨t, ht_mem⟩, ⟨t', ht'_mem⟩
    intro v₁ hv₁ v₂ hv₂
    replace hv₂ := ht'.1 hv₂
    rw [Finset.mem_filter] at hv₂
    replace hv₁ := hv₂.2 hv₁
    rw [mem_neighborFinset] at hv₁
    exact hv₁.symm
  · apply mul_le_mul_of_nonneg_right
    · exact Nat.choose_le_pow_div (card α) (card V)
    · rw [sub_nonneg, Nat.one_le_cast]
      exact Nat.succ_le_of_lt card_pos

/-- This is an auxiliary lemma for the double-counting argument in the proof of the
Kővári–Sós–Turán theorem, counting over vertices. -/
private lemma le_card_aux
    [Nonempty α] [Nonempty V] (h : card α ≤ (∑ v : V, G.degree v : ℝ) / card V) :
    ((card V)*(2*G.edgeFinset.card/(card V)-(card α))^(card α)/(card α).factorial : ℝ)
      ≤ (aux G (card α)).card := by
  have h' : card α-1 ≤ (∑ v, G.degree v : ℝ)/ card V := by
    trans (card α : ℝ)
    · rw [←Nat.cast_pred card_pos, Nat.cast_le]
      exact Nat.pred_le (card α)
    · exact h
  simp_rw [Finset.card_filter _, Finset.sum_product_right, ←Finset.card_filter,
    Finset.powersetCard_eq_filter, Finset.filter_comm, Finset.powerset_univ,
    Finset.filter_subset_univ, ←Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    card_neighborFinset_eq_degree, Nat.cast_sum]
  trans (card V)*((descPochhammer ℝ (card α)).eval
      ((∑ v, G.degree v : ℝ)/(card V))/(card α).factorial)
  · rw [←Nat.cast_two, ←Nat.cast_mul, ←sum_degrees_eq_twice_card_edges, Nat.cast_sum,
      mul_div, div_le_div_iff_of_pos_right (by positivity), mul_le_mul_left (by positivity)]
    trans ((∑ x : V, ↑(G.degree x))/(card V)-(card α)+1)^(card α)
    · apply pow_le_pow_left₀
      · rwa [←sub_nonneg] at h
      · rw [sub_add, sub_le_sub_iff_left, ←Nat.cast_pred card_pos, Nat.cast_le]
        exact Nat.pred_le (card α)
    · exact pow_le_descPochhammer_eval h'
  · rw [←le_inv_mul_iff₀ (by positivity), Finset.mul_sum, div_eq_mul_inv _ (card V : ℝ),
      mul_comm _ (card V : ℝ)⁻¹, Finset.mul_sum]
    apply descPochhammer_eval_div_factorial_le_sum_choose
      (Nat.succ_le_of_lt card_pos) _ _ (by simp) (by field_simp)
    rwa [div_eq_mul_inv, mul_comm, Finset.mul_sum] at h'

/-- The `completeBipartiteGraph α β`-free simple graphs on the vertex type `V` have at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2` edges.

This is the **Kővári–Sós–Turán theorem**. -/
theorem card_edgeFinset_le_of_completeBipartiteGraph_free
    [Nonempty α] (h_card_le : card α ≤ card β) {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_free : (completeBipartiteGraph α β).Free G) :
    G.edgeFinset.card
      ≤ ((card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
        + (card α)*(card V)/2 : ℝ) := by
  have hcardβ : 1 ≤ card β := card_pos.trans_le h_card_le
  haveI : Nonempty β := by
    rwa [←card_pos_iff]
  cases isEmpty_or_nonempty V
  -- if no vertices
  · have h_two_sub_one_div_ne_zero : 2 - (card α : ℝ)⁻¹ ≠ 0 := by
      apply sub_ne_zero_of_ne ∘ ne_of_gt
      apply lt_of_le_of_lt _ one_lt_two
      exact Nat.cast_inv_le_one (card α)
    simp [h_two_sub_one_div_ne_zero]
  -- if vertices
  · cases lt_or_le (∑ v, G.degree v : ℝ) (card α * card V : ℝ) with
    -- if avg degree less than `card a`
    | inl h_avg =>
      rw [←Nat.cast_sum, sum_degrees_eq_twice_card_edges, Nat.cast_mul,
        Nat.cast_two, ←lt_div_iff₀' zero_lt_two] at h_avg
      trans (card α)*(card V)/2
      · exact le_of_lt h_avg
      · apply le_add_of_nonneg_left
        apply div_nonneg _ zero_le_two
        apply mul_nonneg
        · apply Real.rpow_nonneg
          rw [sub_nonneg, Nat.one_le_cast]
          exact Nat.succ_le_of_lt card_pos
        · apply Real.rpow_nonneg
          exact Nat.cast_nonneg (card V)
    -- if avg degree at least `card α`
    | inr h_avg =>
      rw [←le_div_iff₀ (by positivity)] at h_avg
      -- double-counting subsets of cardinality `card α` of neighbor sets
      have h_aux := (le_card_aux h_avg).trans (card_aux_le h_free)
      rwa [mul_comm _ (card β-1 : ℝ), mul_div, div_le_div_iff_of_pos_right,
        mul_comm (card β-1 : ℝ) _, ←Real.rpow_natCast, ←Real.rpow_natCast,
        mul_comm _ ((card β)-1 : ℝ), ←Real.rpow_le_rpow_iff, Real.mul_rpow, Real.mul_rpow,
        Real.rpow_rpow_inv, Real.rpow_rpow_inv, mul_sub, sub_le_iff_le_add, mul_div, div_le_iff₀,
        ←mul_assoc, ←le_div_iff₀', add_mul, add_div, ←div_div,
        div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹: ℝ),
        ←Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ), ←Real.rpow_mul, mul_neg_one, mul_assoc,
        mul_comm (card V : ℝ) _, ←Real.rpow_add_one, mul_assoc, mul_comm (card V : ℝ) _,
        ←Real.rpow_add_one, add_assoc, one_add_one_eq_two, add_comm _ 2, ←sub_eq_add_neg, ←div_div,
        div_eq_mul_inv _ ((card V)^(card α : ℝ)⁻¹ : ℝ),
        ←Real.rpow_neg_one ((card V)^(card α : ℝ)⁻¹ : ℝ), ←Real.rpow_mul, mul_neg_one, mul_assoc,
        mul_comm (card V : ℝ) _, ←Real.rpow_add_one, mul_assoc, mul_comm (card α : ℝ) _,
        ←mul_assoc, ←Real.rpow_add, ←add_assoc, add_neg_cancel, zero_add, Real.rpow_one,
        mul_comm _ (card α : ℝ), inv_eq_one_div] at h_aux
      any_goals
        rw [←Nat.cast_sum, sum_degrees_eq_twice_card_edges,
          Nat.cast_mul, Nat.cast_two, ←sub_nonneg] at h_avg
        positivity
      any_goals
        field_simp [hcardβ]

end KovariSosTuran

/-- The extremal numbers of `completeBipartiteGraph α β` on the type `V` are at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2+(card α)*(card V)/2`.

This is the corollary of the **Kővári–Sós–Turán theorem** for extremal numbers. -/
theorem extremalNumber_completeBipartiteGraph_le [Nonempty α] (h_card_le : card α ≤ card β) :
  extremalNumber V (completeBipartiteGraph α β)
    ≤ (card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
      + (card α : ℝ)*(card V : ℝ)/2 := by
  have hcardβ : 1 ≤ card β := card_pos.trans_le h_card_le
  haveI : Nonempty β := by
    rwa [←card_pos_iff]
  have h_nonneg : 0 ≤ ((card β-1)^(1/(card α : ℝ))*(card V)^(2-1/(card α : ℝ))/2
      + (card α)*(card V)/2 : ℝ) := by
    apply add_nonneg _ (by positivity)
    apply div_nonneg _ zero_le_two
    apply mul_nonneg _ (by positivity)
    apply Real.rpow_nonneg
    rw [sub_nonneg, Nat.one_le_cast]
    exact Nat.succ_le_of_lt card_pos
  rw [extremalNumber_le_iff_of_nonneg V (completeBipartiteGraph α β) h_nonneg]
  intro G _ h_free
  exact card_edgeFinset_le_of_completeBipartiteGraph_free h_card_le h_free

end SimpleGraph
