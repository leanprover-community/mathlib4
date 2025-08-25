/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Data.Real.Sqrt

/-!
# The Erdős-Stone-Simonovits theorem

This file proves the **Erdős-Stone-Simonovits theorem** for simple graphs.

## Main definitions

* `SimpleGraph.completeEquipartiteGraph_isContained_of_minDegree` is the proof of the minimal
  degree version of the **Erdős-Stone theorem** for simple graphs.
-/


open Filter Finset Fintype Real Topology

namespace SimpleGraph

section ErdosStone

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

namespace ErdosStone

variable {ε : ℝ} {r t t' : ℕ} (A : G.completeEquipartiteSubgraph r t')

/-- `filterAdjComplVerts` is the set of vertices in the complement of a complete equipartite
subgraph, in `r` parts each of size `t'`, adjacent to at least `t` vertices in each part of the
complete equipartite subgraph.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
abbrev filterAdjComplVerts (t : ℕ) : Finset V :=
  { v ∈ A.vertsᶜ | ∀ i : Fin r, ∃ s : (A.parts i).val.powersetCard t, ∀ w ∈ s.val, G.Adj v w }

lemma filterAdjComplVerts_subset_compl_verts : filterAdjComplVerts A t ⊆ A.vertsᶜ :=
  filter_subset _ A.vertsᶜ

omit [DecidableRel G.Adj] in
lemma between_verts_isBipartiteWith :
    (G.between A.verts A.vertsᶜ).IsBipartiteWith A.verts ↑A.vertsᶜ := by
  rw [coe_compl A.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

lemma le_card_edgeFinset_between_verts :
    (#A.verts * (G.minDegree - #A.verts) : ℝ) ≤ #(G.between A.verts A.vertsᶜ).edgeFinset := by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith A),
    ← nsmul_eq_mul, ← sum_const, Nat.cast_sum]
  apply sum_le_sum
  intro v hv
  rw [sub_le_iff_le_add]
  exact_mod_cast (minDegree_le_degree G v).trans (degree_le_between_plus hv)

/-- For `v ∈ A.vertsᶜ \ filterAdjComplVerts`, since `v` is adjacent to fewer than `t` vertices
in at least one part of the complete equipartite subgraph, it follows that `v` is adjacent to
fewer than `#A.verts - (t' - t)` vertices in `A.verts`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma degree_between_verts_lt_of_mem_sdiff {v : V} (hv : v ∈ A.vertsᶜ \ filterAdjComplVerts A t) :
    (G.between A.verts A.vertsᶜ).degree v < #A.verts - t' + t := by
  rw [mem_sdiff, mem_filter, not_and_or, and_or_left, and_not_self_iff, false_or] at hv
  push_neg at hv
  obtain ⟨hv, i, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree,
    isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith A) hv,
    filter_disjiUnion, card_disjiUnion, sum_eq_sum_diff_singleton_add (mem_univ i)]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [A.card_verts, ← Nat.sub_one_mul,  ← Fintype.card_fin r,
        ← card_singleton i, ← card_compl, ← smul_eq_mul, ← sum_const]
      enter [2, j]
      rw [← A.card_parts j]
    exact sum_le_sum (fun _ _ ↦ card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s ∈ (A.parts i).val.powersetCard t :=
      powersetCard_mono (filter_subset _ (A.parts i).val) hs
    use ⟨s, hs'⟩
    intro w hw
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

lemma card_edgeFinset_between_verts_le (hr : 0 < r) :
    (#(G.between A.verts A.vertsᶜ).edgeFinset : ℝ)
      ≤ (card V - #A.verts) * (#A.verts - (t' - t)) + #(filterAdjComplVerts A t) * (t' - t) :=
  calc (#(G.between A.verts A.vertsᶜ).edgeFinset : ℝ)
    _ = ∑ v ∈ A.vertsᶜ \ filterAdjComplVerts A t, ((G.between A.verts A.vertsᶜ).degree v : ℝ)
      + ∑ v ∈ filterAdjComplVerts A t, ((G.between A.verts A.vertsᶜ).degree v : ℝ) := by
        rw [sum_sdiff (filter_subset _ A.vertsᶜ), eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith A)
    _ ≤ ∑ _ ∈ A.vertsᶜ \ filterAdjComplVerts A t, (#A.verts - t' + t : ℝ)
      + ∑ _ ∈ filterAdjComplVerts A t, (#A.verts : ℝ) := by
        apply add_le_add
        · apply sum_le_sum
          intro v hv
          rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr).trans_eq A.card_verts.symm),
            ← Nat.cast_add, Nat.cast_le]
          exact (degree_between_verts_lt_of_mem_sdiff A hv).le
        · apply sum_le_sum
          intro v hv
          exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith A) (filterAdjComplVerts_subset_compl_verts A hv)
    _ = (card V - #A.verts) * (#A.verts - (t' - t)) + #(filterAdjComplVerts A t) * (t' - t) := by
        simp_rw [sum_const, card_sdiff (filterAdjComplVerts_subset_compl_verts A), nsmul_eq_mul,
          Nat.cast_sub (card_le_card (filterAdjComplVerts_subset_compl_verts A)), card_compl,
          Nat.cast_sub (card_le_univ A.verts)]
        ring_nf

/-- `#filterAdjComplVerts` is arbitrarily large with respect to `card V`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma mul_le_card_aux_mul (hr : 0 < r) (hδ : G.minDegree ≥ (1 - 1 / r + ε) * card V)
    {x : ℕ} (hx : (x + r * t') * (t' - t) ≤ card V * (t' * r * ε - t)) :
    (x * (t' - t) : ℝ) ≤ (#(filterAdjComplVerts A t) * (t' - t) : ℝ) :=
  calc (x * (t' - t) : ℝ)
    _ ≤ card V * (t' * r * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (x : ℝ) (r * t' : ℝ), sub_mul]
        exact sub_le_sub_right hx _
    _ = #A.verts * ((1 - 1 / r + ε) * card V - #A.verts)
      - (card V - #A.verts) * (#A.verts - (t' - t)) := by
        rw [A.card_verts]
        field_simp
        ring_nf
    _ ≤ #A.verts * (G.minDegree - #A.verts) - (card V - #A.verts) * (#A.verts - (t' - t)) := by
        apply sub_le_sub_right
        apply mul_le_mul_of_nonneg_left (sub_le_sub_right hδ _) (#A.verts).cast_nonneg
    _ ≤ #(filterAdjComplVerts A t) * (t' - t) := by
        apply sub_left_le_of_le_add
        exact (le_card_edgeFinset_between_verts A).trans (card_edgeFinset_between_verts_le A hr)

/-- For `w ∈ filterAdjComplVerts`, there exists a `r` subets of vertices of size `t < t'`
adjacent to `w`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
noncomputable abbrev filterAdjComplVerts.Pi :
    filterAdjComplVerts A t → Π i : Fin r, powersetCard t (A.parts i).val :=
  fun ⟨_, h⟩ i ↦ (Multiset.of_mem_filter h i).choose

lemma filterAdjComplVerts.Pi.mem_val (w : filterAdjComplVerts A t) (i : Fin r) :
    ∀ v ∈ (filterAdjComplVerts.Pi A w i).val, G.Adj w v :=
  (Multiset.of_mem_filter w.prop i).choose_spec

/-- If `#filterAdjComplVerts` is sufficently large, then there exist at least `t` vertices
adjacent to `t` vertices in each `A.parts`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma exists_pi_powersetCard_completeEquipartiteSubgraph_parts
    (hr : 0 < r) (ht_lt_t' : t < t') (hδ : G.minDegree ≥ (1 - 1 / r + ε) * card V)
    (hx : (t'.choose t ^ r * t + r * t') * (t' - t) ≤ card V * (t' * r * ε - t)) :
    ∃ (s : univ.powersetCard t) (y : Π i : Fin r, powersetCard t (A.parts i).val),
      ∀ v₁ ∈ s.val, ∀ i, ∀ v₂ ∈ (y i).val, G.Adj v₁ v₂ := by
  -- there exists at least `t` vertices ...
  have ⟨y, hy⟩ : ∃ y : Π i : Fin r, powersetCard t (A.parts i).val,
      t ≤ #(univ.filter (filterAdjComplVerts.Pi A · = y)) := by
    have : Nonempty (Π i : Fin r, powersetCard t (A.parts i).val) := by
      rw [Classical.nonempty_pi]
      conv =>
        enter [i]
        rw [nonempty_coe_sort, powersetCard_nonempty, A.card_parts]
      exact Function.const (Fin r) ht_lt_t'.le
    apply exists_le_card_fiber_of_mul_le_card
    rw [Fintype.card_pi, card_coe]
    conv =>
      enter [1, 1, 2, i]
      rw [card_coe, card_powersetCard, A.card_parts]
    rw [prod_const, card_univ, Fintype.card_fin, ← @Nat.cast_le ℝ]
    apply le_of_mul_le_mul_right
    · exact (mul_le_card_aux_mul A hr hδ (mod_cast hx))
    · rwa [← @Nat.cast_lt ℝ, ← sub_pos] at ht_lt_t'
  -- ... adjacent to `t` vertices in each `A.parts`
  have ⟨s', hs'⟩ := exists_subset_card_eq hy
  refine ⟨⟨s'.map (Function.Embedding.subtype _),
    mem_powersetCard_univ.mpr ((card_map _).trans hs'.2)⟩, y, ?_⟩
  intro v hv i w hw
  obtain ⟨v', hv', hv⟩ := Finset.mem_map.mp hv
  rw [Function.Embedding.coe_subtype] at hv
  rw [← hv]
  apply filterAdjComplVerts.Pi.mem_val A v' i w
  apply hs'.1 at hv'
  rw [mem_filter] at hv'
  rwa [← hv'.2] at hw

end ErdosStone

/-- If `G` has a minimal degree of at least `(1 - 1 / r + o(1)) * card V`, then `G` contains a copy
of a `completeEquipartiteGraph` in `r + 1` parts each of size `t`.

This is the minimal-degree version of the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_minDegree {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        G.minDegree ≥ (1 - 1 / r + ε) * card V
          → completeEquipartiteGraph (r + 1) t ⊑ G := by
  rcases show (r = 0 ∨ t = 0) ∨ r ≠ 0 ∧ t ≠ 0 by tauto with h0 | ⟨hr, ht⟩
  · rw [← Nat.le_zero_eq, ← @Nat.add_le_add_iff_right r 0 1, zero_add] at h0
    use (r + 1) * t
    intro _ _ _ h_card _ _ _
    rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le,
      card_prod, Fintype.card_fin, Fintype.card_fin]
    exact h_card.le
  · rw [← Nat.pos_iff_ne_zero] at hr ht
    -- choose `ε'` to ensure `G.minDegree` is large enough
    let ε' := 1 / (↑(r - 1) * r) + ε
    have hε' : 0 < ε' := by positivity
    -- choose `t'` larger than `t / (r * ε)`
    let t' := ⌊t / (r * ε)⌋₊ + 1
    have ht_lt_t'rε : t < t' * r * ε := by
      rw [mul_assoc, ← div_lt_iff₀ (by positivity), Nat.cast_add_one]
      exact Nat.lt_floor_add_one (t / (r * ε))
    have ht' : 0 < t' := by positivity
    have ⟨n', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' (r - 1) t'
    -- choose `n` at least `(t'.choose t ^ r * t + r * t') * (t '- t) / (t' * r * ε - t)` to
    -- satisfy the pigeonhole principle
    let n := max n' ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (t' * r * ε - t)⌉₊
    use n
    intro V _ _ h_card G _ hδ
    have : Nonempty V := card_pos_iff.mp (n.zero_le.trans_lt h_card)
    -- `r` is less than `1 / ε` otherwise `G.minDegree = card V`
    have hrε_lt_1 : r * ε < 1 := by
      have hδ_lt_card : (G.minDegree : ℝ) < (card V : ℝ) := mod_cast G.minDegree_lt_card
      contrapose! hδ_lt_card with h1_le_rε
      rw [← div_le_iff₀' (by positivity), ← sub_nonpos,
        ← le_sub_self_iff 1, ← sub_add] at h1_le_rε
      exact hδ.trans' (le_mul_of_one_le_left (card V).cast_nonneg h1_le_rε)
    have ht_lt_t' : t < t' := by
      rw [mul_assoc] at ht_lt_t'rε
      exact_mod_cast ht_lt_t'rε.trans (mul_lt_of_lt_one_right (mod_cast ht') hrε_lt_1)
    -- identify a `completeEquipartiteGraph r t'` in `G` from the inductive hypothesis
    replace ih : completeEquipartiteGraph r t' ⊑ G := by
      rcases eq_or_ne r 1 with hr_eq_1 | hr_ne_1
      -- if `r = 1` then `completeEquipartiteGraph r t' = ⊥`
      · have h0 : r ≤ 1 ∨ t' = 0 := Or.inl hr_eq_1.le
        rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le]
        rw [card_prod, Fintype.card_fin, Fintype.card_fin, hr_eq_1, one_mul]
        apply h_card.le.trans'
        exact_mod_cast calc (t' : ℝ)
          _ ≤ r * t' := le_mul_of_one_le_left (by positivity) (mod_cast hr)
          _ ≤ t'.choose t ^ r * t + r * t' := le_add_of_nonneg_left (by positivity)
          _ ≤ (t'.choose t ^ r * t + r * t') * (t' - t) / (t' * r * ε - t) := by
            rw [mul_div_assoc, le_mul_iff_one_le_right (by positivity),
              one_le_div (sub_pos.mpr ht_lt_t'rε), sub_le_sub_iff_right, mul_assoc,
              mul_le_iff_le_one_right (by positivity)]
            exact hrε_lt_1.le
          _ ≤ ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (t' * r * ε - t)⌉₊ := Nat.le_ceil _
          _ ≤ n := Nat.cast_le.mpr (le_max_right n' _)
      -- if `r > 1` then `G` satisfies the inductive hypothesis
      · have hδ' := calc (G.minDegree : ℝ)
          _ ≥ (1 - 1 / (r - 1) + (1 / (r - 1) - 1 / r) + ε) * card V := by
              rwa [← sub_add_sub_cancel _ (1 / (r - 1) : ℝ) _] at hδ
          _ = (1 - 1 / ↑(r - 1) + ε') * card V := by
              rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                  (sub_ne_zero_of_ne <| mod_cast hr_ne_1) (mod_cast hr.ne'),
                sub_sub_cancel, mul_one, one_div_mul_one_div_rev, mul_comm (r : ℝ) _,
                ← Nat.cast_pred hr, add_assoc]
        rw [← Nat.succ_pred_eq_of_pos hr]
        exact ih (h_card.trans_le' (le_max_left n' _)) hδ'
    obtain ⟨A⟩ := completeEquipartiteGraph_isContained_iff.mp ih
      -- find `t` vertices not in `A` adjacent to `t` vertices in each `A.parts` using the
      -- pigeonhole principle
    obtain ⟨s, y, hs⟩ := by
      apply ErdosStone.exists_pi_powersetCard_completeEquipartiteSubgraph_parts A hr ht_lt_t' hδ
      rw [← div_le_iff₀ (sub_pos_of_lt ht_lt_t'rε)]
      trans (n : ℝ)
      · exact (Nat.le_ceil _).trans (Nat.cast_le.mpr <| le_max_right n' _)
      · exact_mod_cast h_card.le
    -- identify the `t` vertices in each `A.parts` as a `completeEquipartiteSubgraph r t` in `A`
    let A' : G.completeEquipartiteSubgraph r t := by
      refine ⟨fun i ↦ ⟨(y i).val, ?_⟩, ?_⟩
      · have hyi := mem_powersetCard.mp (y i).prop
        exact mem_powersetCard_univ.mpr hyi.2
      · intro i j h v hv w hw
        have hyi := mem_powersetCard.mp (y i).prop
        have hyj := mem_powersetCard.mp (y j).prop
        exact A.Adj h v (hyi.1 hv) w (hyj.1 hw)
    -- identify the `t` vertices not in `A` and the `completeEquipartiteSubgraph r t` in `A`
    -- as a `completeEquipartiteSubgraph (r + 1) t` in `G`
    exact completeEquipartiteGraph_succ_isContained_iff.mpr ⟨A', s, hs⟩

end ErdosStone

end SimpleGraph
