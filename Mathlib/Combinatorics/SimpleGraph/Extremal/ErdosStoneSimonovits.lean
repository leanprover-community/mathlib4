/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Data.Real.Sqrt

/-!
# The Erdős-Stone-Simonovits theorem

This file proves the **Erdős-Stone-Simonovits theorem** for simple graphs.

## Main definitions

* `SimpleGraph.completeEquipartiteGraph_isContained_of_minDegree` is the proof of the minimal
  degree version of the **Erdős-Stone theorem** for simple graphs.

* `SimpleGraph.completeEquipartiteGraph_isContained_of_card_edgeFinset` is the proof of the
  **Erdős-Stone theorem** for simple graphs:

  If `G` has at least `(1 - 1 / r + o(1)) * card V ^ 2 / 2` many edges, then `G` contains a copy of
  a `completeEquipartiteGraph (r + 1) t`.

* `SimpleGraph.lt_extremalNumber_le_of_chromaticNumber` is the proof of the
  **Erdős-Stone-Simonovits theorem** for simple graphs:

  If the chromatic number of `H` equals `r + 1 > 0`, then `extremalNumber` of `H` is greater than
  `(1 - 1 / r - o(1)) * card V ^ 2 / 2` and at most `(1 - 1 / r + o(1)) * card V ^ 2 / 2`.

* `SimpleGraph.isLittleO_extremalNumber_of_chromaticNumber` is the proof of the little-o version of
  the **Erdős-Stone-Simonovits theorem** for simple graphs.

* `SimpleGraph.tendsto_extremalNumber_div_choose_two_of_chromaticNumber` is the proof of the limit
  version of the **Erdős-Stone-Simonovits theorem** for simple graphs.

* `SimpleGraph.turanDensity_eq_of_chromaticNumber` is the proof of the Turán density version of the
  **Erdős-Stone-Simonovits theorem** for simple graphs.

  See `SimpleGraph.turanDensity`.

* `SimpleGraph.isEquivalent_extremalNumber_of_chromaticNumber` is the proof of the equivalence
  version of the **Erdős-Stone-Simonovits theorem** for simple graphs:

  If the chromatic number of `H` equals `r + 1 > 1`, then `extremalNumber n H` is asymptotically
  equivalent to `(1 - 1 / r) * n.choose 2` as `n → ∞`

  See `SimpleGraph.isEquivalent_extremalNumber`.
-/


open Asymptotics Filter Finset Fintype Real Topology

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

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is at least `c * #s`
and count the maximal possible edges removed in the process.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma exists_induce_minDegree_ge_card_edgeFinset_ge {c : ℝ} (hc : 0 ≤ c)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ s : Finset V, (s : Set V) ⊆ G.support ∧ c * #s ≤ (G.induce s).minDegree ∧
      #(G.induce s).edgeFinset
        ≥ #G.edgeFinset - c * (card G.support ^ 2 - #s ^ 2) / 2
          - c * (card G.support - #s) / 2 := by
  by_cases hδ : c * #G.support.toFinset ≤ (G.induce G.support.toFinset).minDegree
  -- if `minDegree` is already at least `c * card G.support`
  · refine ⟨G.support.toFinset, G.support.coe_toFinset.subset, hδ, ?_⟩
    suffices h_card_edges : #(G.induce G.support).edgeFinset ≥ #G.edgeFinset
        - c * (card G.support ^ 2 - #G.support.toFinset ^ 2) / 2
        - c * (card G.support - #G.support.toFinset) / 2 by
      convert h_card_edges
      all_goals exact G.support.coe_toFinset
    rw [card_edgeFinset_induce_support, ← G.support.toFinset_card, sub_self,
      mul_zero,  zero_div, sub_zero, sub_self, mul_zero, zero_div, sub_zero]
  -- if `minDegree` is less than `c * card G.support`
  · replace hδ : (G.induce G.support).minDegree < c * (card G.support) := by
      rw [not_le, G.support.toFinset_card] at hδ
      convert hδ
      all_goals exact G.support.coe_toFinset.symm
    have h_card_support_pos : 0 < card G.support := by
      contrapose! hδ
      rw [Nat.eq_zero_of_le_zero hδ, Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg (G.induce G.support).minDegree
    have : Nonempty G.support := card_pos_iff.mp h_card_support_pos
    -- delete a minimal degree vertex
    have ⟨x, hδ_eq_degx⟩ := exists_minimal_degree_vertex (G.induce G.support)
    let G' := G.deleteIncidenceSet ↑x
    -- repeat the process
    have ⟨s, hs', ihδ', ih_card_edges'⟩ := exists_induce_minDegree_ge_card_edgeFinset_ge hc G'
    have ⟨hs, hx_not_mem⟩ : (s : Set V) ⊆ G.support ∧ ↑x ∉ (s : Set V) := by
      rw [← Set.disjoint_singleton_right, ← Set.subset_diff]
      exact hs'.trans (G.support_deleteIncidenceSet_subset ↑x)
    have ihδ : c * #s ≤ (G.induce s).minDegree := by
      simpa [← induce_deleteIncidenceSet_of_notMem G hx_not_mem] using ihδ'
    have ih_card_edges : #(G.induce s).edgeFinset ≥ #G'.edgeFinset
        - c * (card G'.support ^ 2 - #s ^ 2) / 2 - c * (card G'.support - #s) / 2 := by
      simpa [← G.induce_deleteIncidenceSet_of_notMem hx_not_mem] using ih_card_edges'
    -- use the `s` found at the end of the process
    refine ⟨s, hs, ihδ, ?_⟩
    calc (#(G.induce s).edgeFinset : ℝ)
      _ ≥ #G'.edgeFinset - (c * (card G'.support ^ 2 - #s ^ 2) / 2
        + c * (card G'.support - #s) / 2) := by rwa [sub_sub] at ih_card_edges
      _ ≥ (#G.edgeFinset - c * card G.support) - (c * ((card G.support - 1) ^ 2 - #s ^ 2) / 2
        + c * (card G.support - 1 - #s) / 2) := by
          apply sub_le_sub
          -- exactly `G.minDegree` edges are deleted from the edge set
          · rw [G.card_edgeFinset_deleteIncidenceSet ↑x,
              Nat.cast_sub (G.degree_le_card_edgeFinset x), ← degree_induce_support, ← hδ_eq_degx]
            exact sub_le_sub_left hδ.le #G.edgeFinset
          -- at least one vertex is deleted from the support
          · rw [← add_div, ← add_div, div_le_div_iff_of_pos_right zero_lt_two,
              ← Nat.cast_pred card_pos, ← mul_add, sub_add_sub_comm, ← mul_add, sub_add_sub_comm,
              ← Nat.cast_pow (card G'.support) 2, ← Nat.cast_pow (card G.support - 1) 2]
            apply mul_le_mul_of_nonneg_left _ hc
            apply sub_le_sub (add_le_add _ _) le_rfl
            · exact_mod_cast Nat.pow_le_pow_left (G.card_support_deleteIncidenceSet x.prop) 2
            · exact_mod_cast G.card_support_deleteIncidenceSet x.prop
      _ ≥ #G.edgeFinset - c * (card G.support ^ 2 - #s ^ 2) / 2
        - c * (card G.support - #s) / 2 := by linarith
termination_by card G.support
decreasing_by
  exact (G.card_support_deleteIncidenceSet x.prop).trans_lt (Nat.pred_lt_of_lt h_card_support_pos)

/-- Repeatedly remove minimal degree vertices until `(G.induce s).minDegree` is at least `c * #s`
and `#s ^ 2 ≥ ε * card V ^ 2 - c * card V`, that is, `#s ≈ √ε * card V` when `c ≈ 0`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma exists_induce_minDegree_ge_card_sq_ge {c : ℝ} (hc : 0 ≤ c)
    {ε : ℝ} (h : #G.edgeFinset ≥ (c + ε) * card V ^ 2 / 2) :
    ∃ s : Finset V, c * #s ≤ (G.induce s).minDegree ∧ ε * card V ^ 2 - c * card V ≤ #s ^ 2 := by
  rcases isEmpty_or_nonempty V
  · exact ⟨∅, by simp⟩
  · have ⟨s, _, hδ, hs⟩ := exists_induce_minDegree_ge_card_edgeFinset_ge hc G
    rw [ge_iff_le, sub_sub, sub_le_iff_le_add] at hs
    refine ⟨s, hδ, ?_⟩
    rw [← div_le_div_iff_of_pos_right zero_lt_two, sub_div]
    -- use `#G.edgeFinset ≥ (c + ε) * card V ^ 2 / 2` to bound `#s ^ 2`
    calc ε * card V ^ 2 / 2 - c * card V / 2
      _ = (c + ε) * card V ^ 2 / 2 - (c * card V ^ 2 / 2 + c * card V / 2) := by ring_nf
      _ ≤ #s * (#s - 1) / 2 + (c * (card G.support ^ 2 - #s ^ 2) / 2
        + c * (card G.support - #s) / 2) - (c * card V ^ 2 / 2 + c * card V / 2) := by
          apply sub_le_sub_right
          refine (h.trans hs).trans ?_
          apply add_le_add_right
          rw [← Nat.cast_choose_two, ← card_coe s]
          exact_mod_cast card_edgeFinset_le_card_choose_two
      _ = #s ^ 2 / 2 - (c * (card V ^ 2 - card G.support ^ 2) / 2
        + c * (card V - card G.support) / 2 + c * #s ^ 2 / 2 + c * #s / 2 + #s / 2) := by ring_nf
      _ ≤ #s ^ 2 / 2 := by
          apply sub_le_self
          repeat apply add_nonneg
          all_goals
            try apply div_nonneg _ zero_le_two
            try apply mul_nonneg hc
            try apply sub_nonneg_of_le
            try apply pow_le_pow_left₀
          any_goals positivity
          any_goals exact_mod_cast set_fintype_card_le_univ G.support

/-- If `G` has at least `(1 - 1 / r + o(1)) * card V ^ 2 / 2` many edges, then `G` contains a copy
of a `completeEquipartiteGraph (r + 1) t`.

This is the **Erdős-Stone theorem**. -/
theorem completeEquipartiteGraph_isContained_of_card_edgeFinset {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (1 - 1 / r + ε) * card V ^ 2 / 2
        → completeEquipartiteGraph (r + 1) t ⊑ G := by -- TODO
  -- choose `c + ε' = (1 - 1 / r + ε / 2) + ε / 2 = 1 - 1 / r + ε`
  let ε' := ε / 2
  have hε' : 0 < ε' := by positivity
  let c := 1 - 1 / r + ε / 2
  have hc : 0 < c := add_pos_of_nonneg_of_pos r.one_sub_one_div_cast_nonneg hε'
  -- find `n' > card V` sufficent for the minimal-degree version of the Erdős-Stone theorem
  have ⟨n', ih⟩ := completeEquipartiteGraph_isContained_of_minDegree hε' r t
  use ⌊c / ε' + n' / √ε'⌋₊
  intro V _ _ h_card G _ h
  rw [Nat.floor_lt (by positivity)] at h_card
  -- find `s` such that `G.induce s` has appropriate minimal-degree
  rw [← add_halves ε, ← add_assoc] at h
  obtain ⟨s, hδ, h_cards_sq⟩ := exists_induce_minDegree_ge_card_sq_ge hc.le h
  -- assume `#s` is sufficently large
  suffices h_cards_sq : (n' ^ 2 : ℝ) < (#s ^ 2 : ℝ) by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_lt,
      Nat.pow_lt_pow_iff_left two_ne_zero] at h_cards_sq
    -- find `completeEquipartiteGraph` from minimal-degree version of the Erdős-Stone theorem
    simp_rw [← card_coe, ← Finset.coe_sort_coe] at h_cards_sq hδ
    exact (ih h_cards_sq hδ).trans ⟨Copy.induce G s⟩
  -- `x ↦ ε' * x ^ 2 - c * x` is strictly monotonic on `[c / (2 * ε'), ∞)`
  have h_strictMonoOn : StrictMonoOn (fun x ↦ ε' * x ^ 2 - c * x) (Set.Ici (c / (2 * ε'))) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (Continuous.continuousOn (by continuity))
    intro x hx
    rw [deriv_fun_sub, deriv_const_mul, deriv_fun_pow, Nat.cast_two, pow_one, deriv_id'', mul_one,
      ← mul_assoc ε' 2 x, mul_comm ε' 2, deriv_const_mul, deriv_id'', mul_one, sub_pos,
      ← div_lt_iff₀' (mul_pos two_pos hε')]
    rwa [interior_Ici, Set.mem_Ioi] at hx
    all_goals
      try apply DifferentiableAt.const_mul
      try apply DifferentiableAt.pow
      exact differentiableAt_fun_id
  -- prove `#s` is sufficently large
  calc (#s ^ 2 : ℝ)
    _ ≥ ε'* card V ^ 2 - c * card V := h_cards_sq
    _ > ε' * (c / ε' + n' / √ε') ^ 2 - c * (c / ε' + n' / √ε') := by
        have h_le : c / (2 * ε') ≤ c / ε' + n' / √ε' := by
          trans c / ε'
          · rw [mul_comm, ← div_div, half_le_self_iff]
            exact div_nonneg hc.le hε'.le
          · rw [le_add_iff_nonneg_right]
            exact div_nonneg n'.cast_nonneg (sqrt_nonneg ε')
        exact h_strictMonoOn h_le (h_le.trans h_card.le) h_card
    _ = n' ^ 2 + n' * c / sqrt ε' := by
        rw [add_pow_two, mul_add ε', div_pow _ √ε', sq_sqrt hε'.le,
          mul_div_cancel₀ _ hε'.ne', add_comm _ (n' ^ 2 : ℝ), add_sub_assoc, add_right_inj,
          mul_add ε' _ _, mul_add c _ _, add_sub_add_comm, div_pow c ε' 2, pow_two ε',
          ← mul_div_assoc ε' _ _, mul_div_mul_left _ _ hε'.ne', ← mul_div_assoc c c ε',
          ← pow_two c, sub_self, zero_add, mul_comm ε' _, mul_assoc _ _ ε', mul_mul_mul_comm,
          div_mul_cancel₀ _ hε'.ne', mul_assoc 2 _ c, ← mul_div_right_comm _ c √ε',
          ← mul_div_assoc c _ √ε', mul_comm c _, two_mul, add_sub_assoc, sub_self, add_zero]
    _ ≥ n' ^ 2 := le_add_of_nonneg_right (by positivity)

end ErdosStone

section ErdosStoneSimonovits

/-- If `ε > 2 * r / n` then a `completeEquipartiteGraph` in `r` parts each of size `⌊n / r⌋` has
more than `(1 - 1 / r - ε) * n ^ 2 / 2` edges.

This is an auxiliary definition for the **Erdős-Stone-Simonovits theorem**. -/
lemma card_edgeFinset_completeEquipartiteGraph_gt {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    ∀ ε > (2 * r / n : ℝ), (1 - 1 / r - ε) * n ^ 2 / 2
      < #(completeEquipartiteGraph r (n / r)).edgeFinset := by
  intro ε hε
  calc (1 - 1 / r - ε) * n ^ 2 / 2
    _ < (1 - 1 / r) * n ^ 2 / 2 - r * n := by
        rw [sub_mul, sub_div, sub_lt_sub_iff_left,
          lt_div_iff₀ zero_lt_two, mul_comm, ← mul_assoc, pow_two, ← mul_assoc]
        apply mul_lt_mul_of_pos_right _ (mod_cast hn)
        rwa [gt_iff_lt, div_lt_iff₀ (by positivity)] at hε
    _ = (1 - 1 / r) * r ^ 2 * (n / r : ℕ) ^ 2 / 2
      - (r * n - (1 - 1 / r) * (n * ↑(n % r)) + (1 - 1 / r) * ↑(n % r) ^ 2 / 2) := by
        conv =>
          enter [1, 1]
          rw [← n.div_add_mod r, Nat.cast_add, add_sq, add_assoc,
            mul_add, add_div, Nat.cast_mul, mul_pow, ← mul_assoc]
        rw [← Nat.cast_mul,
          ← Nat.sub_eq_of_eq_add (Nat.div_add_mod n r).symm, Nat.cast_sub (n.mod_le r)]
        ring_nf
    _ ≤ (1 - 1 / r) * r ^ 2 * (n / r : ℕ) ^ 2 / 2 := by
        apply sub_le_self
        apply add_nonneg
        · rw [sub_nonneg, ← mul_assoc, mul_comm (r : ℝ) (n : ℝ)]
          apply mul_le_mul _ (mod_cast (n.mod_lt hr).le) (n % r).cast_nonneg (mod_cast hn.le)
          exact mul_le_of_le_one_left (mod_cast hn.le) r.one_sub_one_div_cast_le_one
        · apply div_nonneg _ zero_le_two
          exact mul_nonneg (r.one_sub_one_div_cast_nonneg) (by positivity)
    _ = #(completeEquipartiteGraph r (n / r)).edgeFinset := by
        simp_rw [card_edgeFinset_completeEquipartiteGraph,
          Nat.cast_mul, Nat.cast_pow,  Nat.cast_choose_two]
        field_simp
        ring_nf

variable {W : Type*} [Fintype W] {H : SimpleGraph W}

omit [Fintype W] in
lemma lt_extremalNumber_of_not_colorable {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 0 < r) (nhc : ¬H.Colorable r) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      (1 - 1 / r - ε) * card V ^ 2 / 2 < extremalNumber (card V) H := by
  use ⌊2 * r / ε⌋₊
  intro V _ _ h_card
  have : Nonempty V := card_pos_iff.mp (Nat.zero_lt_of_lt h_card)
  let G := completeEquipartiteGraph r (card V / r)
  -- `completeEquipartiteGraph` is `r`-colorable
  have : Nonempty (Fin r × Fin (card V / r) ↪ V) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [card_prod, Fintype.card_fin, Fintype.card_fin]
    exact (card V).mul_div_le r
  let f := Classical.arbitrary (Fin r × Fin (card V / r) ↪ V)
  -- `completeEquipartiteGraph` has sufficently many edges
  have h_card_edges : #G.edgeFinset > (1 - 1 / r - ε) * card V ^ 2 / 2 := by
    apply card_edgeFinset_completeEquipartiteGraph_gt hr card_pos ε
    rwa [Nat.floor_lt (by positivity), div_lt_iff₀' hε, ← div_lt_iff₀ (by positivity)] at h_card
  rw [← G.card_edgeFinset_map f] at h_card_edges
  apply lt_of_lt_of_le h_card_edges
  rw [Nat.cast_le]
  -- `H` is not contained in `completeEquipartiteGraph`
  apply card_edgeFinset_le_extremalNumber
  have : NeZero r := ⟨hr.ne'⟩
  exact free_of_colorable nhc (completeEquipartiteGraph_colorable.map f)

lemma extremalNumber_le_of_colorable {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hc : H.Colorable (r + 1)) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      extremalNumber (card V) H ≤ (1 - 1 / r + ε) * card V ^ 2 / 2 := by
  obtain ⟨C⟩ := hc
  let f := fun c ↦ card (C.colorClass c)
  let t := univ.sup f
  have h₁ : H ⊑ completeEquipartiteGraph (r + 1) t := by
    apply isContained_completeEquipartiteGraph_of_colorable C t
    intro c
    rw [show card (C.colorClass c) = f c from rfl]
    exact le_sup (mem_univ c)
  have ⟨n, h₂⟩ := completeEquipartiteGraph_isContained_of_card_edgeFinset hε r t
  use n
  intro V _ _ h_card
  trans (extremalNumber (card V) (completeEquipartiteGraph (r + 1) t) : ℝ)
  -- `H` is contained in `completeEquipartiteGraph`
  · exact_mod_cast h₁.extremalNumber_le
  -- `completeEquipartiteGraph` is contained in `G`
  · have : 0 ≤ 1 - 1 / r + ε := add_nonneg r.one_sub_one_div_cast_nonneg hε.le
    rw [extremalNumber_le_iff_of_nonneg _ (by positivity)]
    intro _ _ h
    contrapose! h
    rw [not_free]
    exact h₂ h_card h.le

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the `extremalNumber` of `H` is greater
than `(1 - 1 / r - o(1)) * card V ^ 2 / 2` and at most `(1 - 1 / r + o(1)) * card V ^ 2 / 2`.

This is the **Erdős-Stone-Simonovits theorem**. -/
theorem lt_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    ∃ n, ∀ {V : Type*} [Fintype V] [DecidableEq V], n < card V →
      (1 - 1 / r - ε) * card V ^ 2 / 2 < extremalNumber (card V) H ∧
      extremalNumber (card V) H ≤ (1 - 1 / r + ε) * card V ^ 2 / 2 := by
  have ⟨hc, nhc⟩ := chromaticNumber_eq_iff_colorable_not_colorable.mp hχ
  have ⟨n₁, h₁⟩ := lt_extremalNumber_of_not_colorable hε hr nhc
  have ⟨n₂, h₂⟩ := extremalNumber_le_of_colorable hε hc
  use max n₁ n₂
  intro _ _ _ h_card
  have h_card₁ := h_card.trans_le' (Nat.le_max_left n₁ n₂)
  have h_card₂ := h_card.trans_le' (Nat.le_max_right n₁ n₂)
  exact ⟨h₁ h_card₁, h₂ h_card₂⟩

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the `extremalNumber` of `H` is equal
to `(1 - 1 / r + o(1)) * n ^ 2 / 2`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isLittleO_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    (fun (n : ℕ) ↦ (extremalNumber n H - (1 - 1 / r) * n ^ 2 / 2 : ℝ))
      =o[atTop] (fun (n : ℕ) ↦ (n ^ 2 : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  rw [eventually_atTop]
  have ⟨n₀, h⟩ := lt_extremalNumber_le_of_chromaticNumber hε hr hχ
  use n₀ + 1
  intro n (hn : n₀ < n)
  rw [← Fintype.card_fin n] at hn
  specialize h hn
  rw [Fintype.card_fin] at h
  rw [norm_eq_abs, ← abs_of_pos hε, norm_eq_abs, ← abs_mul]
  apply abs_le_abs
  all_goals linarith

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the limit
`extremalNumber n H / n.choose 2` approaches `1 - 1 / r` as `n → ∞`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem tendsto_extremalNumber_div_choose_two_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r + 1) :
    Tendsto (fun (n : ℕ) ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (1 - 1 / r)) := by
  have h_littleo := IsLittleO.trans_isTheta
    (isLittleO_extremalNumber_of_chromaticNumber hr hχ) (isTheta_choose 2).symm
  have h_tendsto : Tendsto (fun (n : ℕ) ↦ (n ^ 2 / 2 / n.choose 2 : ℝ)) atTop (𝓝 1) := by
    have hz : ∀ᶠ (n : ℕ) in atTop, (n.choose 2 : ℝ) ≠ 0 :=
      eventually_atTop.mpr ⟨2, fun _ h ↦ mod_cast (Nat.choose_pos h).ne'⟩
    simpa only [isEquivalent_iff_tendsto_one hz] using (isEquivalent_choose 2).symm
  simpa [sub_div, ← mul_div]
    using h_littleo.tendsto_div_nhds_zero.add (h_tendsto.const_mul (1 - 1 / r : ℝ))

/-- If the chromatic number of `H` equals `r + 1 > 0`, then the Turán density of `H`
equals `1 - 1 / r`.

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem turanDensity_eq_of_chromaticNumber
    {r : ℕ} (hr : 0 < r) (hχ : H.chromaticNumber = r + 1) : turanDensity H = 1 - 1 / r :=
  (tendsto_extremalNumber_div_choose_two_of_chromaticNumber hr hχ).limUnder_eq

/-- If the chromatic number of `H` equals `r + 1 > 1`, then `extremalNumber n H` is
asymptotically equivalent to `(1 - 1 / r) * n.choose 2` as `n → ∞`

This is a corollary of the **Erdős-Stone-Simonovits theorem**. -/
theorem isEquivalent_extremalNumber_of_chromaticNumber
    {r : ℕ} (hr : 1 < r) (hχ : H.chromaticNumber = r + 1) :
    (fun (n : ℕ) ↦ (extremalNumber n H : ℝ))
      ~[atTop] (fun (n : ℕ) ↦ ((1 - 1 / r) * n.choose 2 : ℝ)) := by
  have hπ_eq : turanDensity H = 1 - 1 / r := turanDensity_eq_of_chromaticNumber (by positivity) hχ
  have hπ_pos : 0 < turanDensity H := by
    rw [hπ_eq, sub_pos, one_div]
    exact inv_lt_one_of_one_lt₀ (mod_cast hr)
  rw [← hπ_eq]
  exact isEquivalent_extremalNumber hπ_pos.ne'

end ErdosStoneSimonovits

end SimpleGraph
