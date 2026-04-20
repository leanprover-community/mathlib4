/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Data.Real.Sqrt

/-!
# The Erdős-Stone-Simonovits theorem

This file proves the **Erdős-Stone-Simonovits theorem** for simple graphs.

## Main definitions

* `SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree` is the proof of the
  minimal degree version of the **Erdős-Stone theorem** for simple graphs.
-/


open Filter Finset Fintype Real Topology

namespace SimpleGraph

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {W : Type*} [Fintype W] {H : SimpleGraph W}

section ErdosStone

namespace ErdosStone

variable {ε : ℝ} {r t t' : ℕ} (K : G.CompleteEquipartiteSubgraph r t')

/-- `ErdosStone.filter` is the set of vertices in the complement of a complete equipartite
subgraph, in `r` parts each of size `t'`, adjacent to at least `t` vertices in each part of the
complete equipartite subgraph.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
def filter (t : ℕ) : Finset (Fin n) :=
  { v ∈ K.vertsᶜ | ∀ p ∈ K.parts, ∃ s ∈ p.powersetCard t, ∀ w ∈ s, G.Adj v w }

theorem filter_subset_compl_verts : filter K t ⊆ K.vertsᶜ :=
  filter_subset _ K.vertsᶜ

omit [DecidableRel G.Adj] in
theorem between_verts_isBipartiteWith :
    (G.between K.verts K.vertsᶜ).IsBipartiteWith K.verts ↑K.vertsᶜ := by
  rw [coe_compl K.verts]
  exact between_isBipartiteWith (disjoint_compl_right)

lemma le_card_edgeFinset_between_verts :
    (#K.verts * (G.minDegree - #K.verts) : ℝ) ≤ #(G.between K.verts K.vertsᶜ).edgeFinset := by
  rw [← isBipartiteWith_sum_degrees_eq_card_edges (between_verts_isBipartiteWith K),
    ← nsmul_eq_mul, ← sum_const, Nat.cast_sum]
  exact sum_le_sum (fun v hv ↦ sub_le_iff_le_add.mpr <|
    mod_cast (G.minDegree_le_degree v).trans (degree_le_between_add hv))

/-- For `v ∈ K.vertsᶜ \ ErdosStone.filter`, since `v` is adjacent to fewer than `t`
vertices in at least one part of the complete equipartite subgraph, it follows that `v` is
adjacent to fewer than `#K.verts - (t' - t)` vertices in `K.verts`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
lemma degree_between_verts_lt_of_mem_sdiff
    {v : Fin n} (hv : v ∈ K.vertsᶜ \ filter K t) (ht'_pos : 0 < t') :
    (G.between K.verts K.vertsᶜ).degree v < #K.verts - t' + t := by
  simp_rw [Finset.mem_sdiff, ErdosStone.filter, mem_filter, not_and_or, and_or_left,
    and_not_self_iff, false_or, not_forall, not_exists, not_and_or, not_forall, exists_prop] at hv
  obtain ⟨hv, p, hp, hs⟩ := hv
  rw [← card_neighborFinset_eq_degree,
    isBipartiteWith_neighborFinset' (between_verts_isBipartiteWith K) hv]
  conv =>
    enter [1, 1, 2]
    unfold CompleteEquipartiteSubgraph.verts
  rw [filter_disjiUnion, card_disjiUnion, sum_eq_sum_diff_singleton_add hp]
  apply add_lt_add_of_le_of_lt
  · conv_rhs =>
      rw [K.card_verts, ← Nat.sub_one_mul, ← K.card_parts.resolve_right ht'_pos.ne',
        ← card_singleton p, ← Finset.card_sdiff_of_subset (singleton_subset_iff.mpr hp),
        ← smul_eq_mul, ← sum_const,
        ← Finset.sum_congr rfl fun _ h ↦ K.card_mem_parts (mem_sdiff.mp h).1]
    exact sum_le_sum (fun _ _ ↦ card_filter_le _ _)
  · contrapose! hs
    obtain ⟨s, hs⟩ := powersetCard_nonempty.mpr hs
    have hs' : s ∈ p.powersetCard t := powersetCard_mono (filter_subset _ _) hs
    refine ⟨s, hs', fun w hw ↦ ?_⟩
    obtain ⟨_, hadj, _⟩ := by
      rw [mem_powersetCard] at hs
      apply hs.1 at hw
      rwa [mem_filter, between_adj] at hw
    exact hadj.symm

lemma card_edgeFinset_between_verts_le (hr_pos : 0 < r) (ht'_pos : 0 < t') :
    (#(G.between K.verts K.vertsᶜ).edgeFinset : ℝ)
      ≤ (n - #K.verts) * (#K.verts - (t' - t))
        + #(filter K t) * (t' - t) :=
  calc (#(G.between K.verts K.vertsᶜ).edgeFinset : ℝ)
    _ = ∑ v ∈ K.vertsᶜ \ filter K t, ((G.between K.verts K.vertsᶜ).degree v : ℝ)
      + ∑ v ∈ filter K t, ((G.between K.verts K.vertsᶜ).degree v : ℝ) := by
        rw [ErdosStone.filter, sum_sdiff (filter_subset _ K.vertsᶜ), eq_comm]
        exact_mod_cast isBipartiteWith_sum_degrees_eq_card_edges'
          (between_verts_isBipartiteWith K)
    _ ≤ ∑ _ ∈ K.vertsᶜ \ filter K t, (#K.verts - t' + t : ℝ)
      + ∑ _ ∈ filter K t, (#K.verts : ℝ) := by
        apply add_le_add <;> refine sum_le_sum (fun v hv ↦ ?_)
        · rw [← Nat.cast_sub ((Nat.le_mul_of_pos_left t' hr_pos).trans_eq K.card_verts.symm)]
          exact_mod_cast (degree_between_verts_lt_of_mem_sdiff K hv ht'_pos).le
        · exact_mod_cast isBipartiteWith_degree_le'
            (between_verts_isBipartiteWith K) (filter_subset_compl_verts K hv)
    _ = (n - #K.verts) * (#K.verts - (t' - t))
      + #(filter K t) * (t' - t) := by
        rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset (filter_subset_compl_verts K),
          Nat.cast_sub (card_le_card (filter_subset_compl_verts K)), card_compl,
          Nat.cast_sub (card_le_univ K.verts), Fintype.card_fin, sum_const, nsmul_eq_mul, sub_mul,
          sub_add (#K.verts : ℝ) _ _, mul_sub (#(filter K t) : ℝ) _ _,
          ← sub_add, sub_add_eq_add_sub, sub_add_cancel]

/-- `#ErdosStone.filter` is arbitrarily large with respect to `n`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
theorem mul_le_card_filter_mul (hr_pos : 0 < r) (ht'_pos : 0 < t')
    (hδ : G.minDegree ≥ (1 - 1 / r + ε) * n)
    {N : ℕ} (hN : (N + r * t') * (t' - t) ≤ n * (r * t' * ε - t)) :
    (N * (t' - t) : ℝ) ≤ (#(filter K t) * (t' - t) : ℝ) :=
  calc (N * (t' - t) : ℝ)
    _ ≤ n * (r * t' * ε - t) - r * t' * (t' - t) := by
        rw [← add_sub_cancel_right (N : ℝ) (r * t' : ℝ), sub_mul]
        exact sub_le_sub_right hN _
    _ = #K.verts * ((1 - 1 / r + ε) * n - #K.verts)
      - (n - #K.verts) * (#K.verts - (t' - t)) := by
        conv_rhs => rw [sub_eq_add_neg, ← neg_mul, neg_sub, sub_mul, mul_sub, ← add_sub_assoc,
          mul_sub, ← add_sub_assoc, sub_add_cancel, sub_right_comm, ← mul_assoc, ← mul_rotate,
          mul_assoc, ← mul_sub, mul_add, mul_sub (#K.verts : ℝ) _ _, mul_one,
          sub_add_eq_add_sub, add_sub_assoc, add_sub_sub_cancel, K.card_verts, Nat.cast_mul,
          mul_one_div, mul_div_cancel_left₀ (t' : ℝ) (mod_cast hr_pos.ne'), sub_add_sub_cancel]
    _ ≤ #K.verts * (G.minDegree - #K.verts) - (n - #K.verts) * (#K.verts - (t' - t)) :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hδ _) (#K.verts).cast_nonneg) _
    _ ≤ #(filter K t) * (t' - t) :=
        sub_left_le_of_le_add <| (le_card_edgeFinset_between_verts K).trans
          (card_edgeFinset_between_verts_le K hr_pos ht'_pos)

/-- For `w ∈ ErdosStone.filter`, there exists a `r` subets of vertices of size `t < t'`
adjacent to `w`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
noncomputable def filter.pi :
    filter K t → K.parts.pi (·.powersetCard t) :=
  fun ⟨_, h⟩ ↦
    let s := Multiset.of_mem_filter h
    ⟨fun p hp ↦ (s p hp).choose, Finset.mem_pi.mpr fun p hp ↦ (s p hp).choose_spec.1⟩

theorem filter.pi.mem_val {p} (hp : p ∈ K.parts) (w : filter K t) :
    ∀ v ∈ (filter.pi K w).val p hp, G.Adj w v :=
  let s := Multiset.of_mem_filter w.prop p hp
  s.choose_spec.right

/-- If `#ErdosStone.filter` is sufficiently large, then there exist a `y` such that there
are least `t` vertices in the fiber `ErdosStone.filter.pi A · = y`.

This is an auxiliary definition for the **Erdős-Stone theorem**. -/
theorem filter.pi.exists_le_card_fiber (hr_pos : 0 < r) (ht'_pos : 0 < t')
    (ht_lt_t' : t < t') (hδ : G.minDegree ≥ (1 - 1 / r + ε) * n)
    (hN : (t'.choose t ^ r * t + r * t') * (t' - t) ≤ n * (r * t' * ε - t)) :
    ∃ y : K.parts.pi (·.powersetCard t), t ≤ #{ w | filter.pi K w = y } := by
  have : Nonempty (K.parts.pi (·.powersetCard t)) := by
    simp_rw [nonempty_coe_sort, pi_nonempty, powersetCard_nonempty]
    intro p hp
    rw [K.card_mem_parts hp]
    exact ht_lt_t'.le
  apply exists_le_card_fiber_of_mul_le_card
  simp_rw [card_coe]
  calc #(K.parts.pi (·.powersetCard t)) * t
    _ = (∏ x ∈ K.parts, (#x).choose t) * t := by
        simp_rw [Finset.card_pi, card_powersetCard]
    _ = (∏ p ∈ K.parts, t'.choose t) * t :=
        congrArg (· * t) <| prod_congr rfl
          fun p hp ↦ congrArg (Nat.choose · t) <| K.card_mem_parts hp
    _ ≤ t'.choose t ^ r * t := by
        rw [prod_const, K.card_parts.resolve_right ht'_pos.ne']
    _ ≤ #(filter K t) := by
        refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt ht_lt_t')
        rw [← @Nat.cast_le ℝ, Nat.cast_mul _ (t' - t), Nat.cast_mul _ (t' - t),
          Nat.cast_sub ht_lt_t'.le]
        exact mul_le_card_filter_mul K hr_pos ht'_pos hδ (mod_cast hN)

end ErdosStone

/-- If `G` has a minimal degree of at least `(1 - 1 / r + o(1)) * n`, then `G` contains a
copy of a `completeEquipartiteGraph` in `r + 1` parts each of size `t`.

This is the minimal-degree version of the **Erdős-Stone theorem**. -/
public theorem eventually_completeEquipartiteGraph_isContained_of_minDegree
    {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
    ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      G.minDegree ≥ (1 - 1 / r + ε) * n
        → completeEquipartiteGraph (r + 1) t ⊑ G := by
  rcases show (r = 0 ∨ t = 0) ∨ r ≠ 0 ∧ t ≠ 0 by tauto with h0 | ⟨hr_pos, ht_pos⟩
  · rw [← Nat.le_zero_eq, ← @Nat.add_le_add_iff_right r 0 1, zero_add] at h0
    rw [eventually_atTop]
    refine ⟨(r + 1) * t, fun n hn {G} _ _ ↦ ?_⟩
    rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le,
      card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    exact hn
  · rw [← Nat.pos_iff_ne_zero] at hr_pos ht_pos
    -- choose `ε'` to ensure `G.minDegree` is large enough
    let ε' := 1 / (↑(r - 1) * r) + ε
    have hε' : 0 < ε' := by positivity
    -- choose `t'` larger than `t / (r * ε)`
    let t' := ⌊t / (r * ε)⌋₊ + 1
    have ht_lt_rt'ε : t < r * t' * ε := by
      rw [mul_comm (r : ℝ) (t' : ℝ), mul_assoc, ← div_lt_iff₀ (by positivity), Nat.cast_add_one]
      exact Nat.lt_floor_add_one (t / (r * ε))
    have ht'_pos : 0 < t' := by positivity
    have ⟨N', ih⟩ := eventually_atTop.mp <|
      eventually_completeEquipartiteGraph_isContained_of_minDegree hε' (r - 1) t'
    -- choose `N` at least `(t'.choose t ^ r * t + r * t') * (t '- t) / (r * t' * ε - t)` to
    -- satisfy the pigeonhole principle
    let N := max (max 1 N') ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊
    refine eventually_atTop.mpr ⟨N, fun n hn {G} _ hδ ↦ ?_⟩
    have : Nonempty (Fin n) := by
      rw [← Fin.pos_iff_nonempty]
      exact hn.trans_lt' (lt_max_of_lt_left (lt_max_of_lt_left zero_lt_one))
    -- `r` is less than `1 / ε` otherwise `G.minDegree = n`
    have hrε_lt_1 : r * ε < 1 := by
      have hδ_lt_card : (G.minDegree : ℝ) < (n : ℝ) := by
        conv_rhs =>
          rw [← Fintype.card_fin n]
        exact_mod_cast G.minDegree_lt_card
      contrapose! hδ_lt_card with h1_le_rε
      rw [← div_le_iff₀' (by positivity), ← sub_nonpos,
        ← le_sub_self_iff 1, ← sub_add] at h1_le_rε
      exact hδ.trans' (le_mul_of_one_le_left n.cast_nonneg h1_le_rε)
    have ht_lt_t' : t < t' := by
      rw [mul_comm (r : ℝ) (t' : ℝ), mul_assoc] at ht_lt_rt'ε
      exact_mod_cast ht_lt_rt'ε.trans_le (mul_le_of_le_one_right (mod_cast ht'_pos.le) hrε_lt_1.le)
    -- identify a `completeEquipartiteGraph r t'` in `G` from the inductive hypothesis
    replace ih : completeEquipartiteGraph r t' ⊑ G := by
      rcases eq_or_ne r 1 with hr_eq_1 | hr_ne_1
      -- if `r = 1` then `completeEquipartiteGraph r t' = ⊥`
      · have h0 : r ≤ 1 ∨ t' = 0 := Or.inl hr_eq_1.le
        rw [completeEquipartiteGraph_eq_bot_iff.mpr h0, bot_isContained_iff_card_le,
          card_prod, Fintype.card_fin, Fintype.card_fin, hr_eq_1, one_mul, Fintype.card_fin]
        apply hn.trans'
        exact_mod_cast calc (t' : ℝ)
          _ ≤ r * t' := le_mul_of_one_le_left (by positivity) (mod_cast hr_pos)
          _ ≤ t'.choose t ^ r * t + r * t' := le_add_of_nonneg_left (by positivity)
          _ ≤ (t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t) := by
            rw [mul_div_assoc, le_mul_iff_one_le_right (by positivity),
              one_le_div (sub_pos.mpr ht_lt_rt'ε), sub_le_sub_iff_right,
              mul_comm (r : ℝ) (t' : ℝ),  mul_assoc, mul_le_iff_le_one_right (by positivity)]
            exact hrε_lt_1.le
          _ ≤ ⌈(t'.choose t ^ r * t + r * t') * (t' - t) / (r * t' * ε - t)⌉₊ := Nat.le_ceil _
          _ ≤ N := Nat.cast_le.mpr (le_max_right _ _)
      -- if `r > 1` then `G` satisfies the inductive hypothesis
      · have hδ' := calc (G.minDegree : ℝ)
          _ ≥ (1 - 1 / (r - 1) + (1 / (r - 1) - 1 / r) + ε) * n := by
              rwa [← sub_add_sub_cancel _ (1 / (r - 1) : ℝ) _] at hδ
          _ = (1 - 1 / ↑(r - 1) + ε') * n := by
              rw [← one_div_mul_sub_mul_one_div_eq_one_div_add_one_div
                (sub_ne_zero_of_ne (mod_cast hr_ne_1)) (mod_cast hr_pos.ne'),
                sub_sub_cancel, mul_one, one_div_mul_one_div_rev, mul_comm (r : ℝ) _,
                ← Nat.cast_pred hr_pos, add_assoc]
        rw [← Nat.succ_pred_eq_of_pos hr_pos]
        exact ih n (hn.trans' (le_max_of_le_left (le_max_right 1 N'))) hδ'
    obtain ⟨K⟩ := completeEquipartiteGraph_isContained_iff.mp ih
    -- find `t` vertices not in `K` adjacent to `t` vertices in each `K.parts` using the
    -- pigeonhole principle
    obtain ⟨⟨y, hy⟩, ht_le_card_filter⟩ := by classical
      apply ErdosStone.filter.pi.exists_le_card_fiber K hr_pos ht'_pos ht_lt_t' hδ
      rw [← div_le_iff₀ (sub_pos_of_lt ht_lt_rt'ε)]
      trans (N : ℝ)
      · exact (Nat.le_ceil _).trans (Nat.cast_le.mpr <| le_max_right _ _)
      · exact_mod_cast hn
    rw [Finset.mem_pi] at hy
    have ⟨s, hs_subset, hcards⟩ := exists_subset_card_eq ht_le_card_filter
    -- identify the `t` vertices in each `K.parts` as a `CompleteEquipartiteSubgraph r t` in `K`
    let K' : G.CompleteEquipartiteSubgraph r t := by
      refine ⟨univ.map ⟨fun p : K.parts ↦ y p.val p.prop, fun p₁ p₂ (heq : y p₁ _ = y p₂ _) ↦ ?_⟩,
        ?_, fun {p} hp ↦ ?_, fun p₁ hp₁ p₂ hp₂ hne v₁ hv₁ v₂ hv₂ ↦ ?_⟩
      · have hy₁' := mem_powersetCard.mp (hy p₁.val p₁.prop)
        have hy₂' := mem_powersetCard.mp (hy p₂.val p₂.prop)
        rw [← heq] at hy₂'
        obtain ⟨v, hv⟩ : (y p₁ _).Nonempty := by
          rw [← Finset.card_pos, hy₁'.right]
          exact ht_pos
        by_contra! hne
        absurd K.isCompleteBetween p₁.prop p₂.prop
          (Subtype.ext_iff.ne.mp hne) (hy₁'.left hv) (hy₂'.left hv)
        exact G.loopless.irrefl v
      · simp_rw [card_map, card_univ, card_coe]
        exact .inl (K.card_parts.resolve_right ht'_pos.ne')
      · simp_rw [univ_eq_attach, Finset.mem_map, mem_attach,
          Function.Embedding.coeFn_mk, true_and, Subtype.exists] at hp
        replace ⟨p, hp, hyp⟩ := hp
        rw [← hyp]
        have hy' := mem_powersetCard.mp (hy p hp)
        exact hy'.right
      · simp_rw [univ_eq_attach, coe_map, Function.Embedding.coeFn_mk,
          Set.mem_image, mem_coe, mem_attach, true_and, Subtype.exists] at hp₁ hp₂
        replace ⟨p₁, hp₁, hyp₁⟩ := hp₁
        rw [← hyp₁] at hv₁ hne
        have hy₁' := mem_powersetCard.mp (hy p₁ hp₁)
        replace ⟨p₂, hp₂, hyp₂⟩ := hp₂
        rw [← hyp₂] at hv₂ hne
        have hy₂' := mem_powersetCard.mp (hy p₂ hp₂)
        refine K.isCompleteBetween hp₁ hp₂ ?_ (hy₁'.left hv₁) (hy₂'.left hv₂)
        by_contra! heq
        simp [← heq] at hne
    -- identify the `t` vertices not in `K` and the `CompleteEquipartiteSubgraph r t` in `K`
    -- as a `CompleteEquipartiteSubgraph (r + 1) t` in `G`
    refine completeEquipartiteGraph_succ_isContained_iff.mpr
      ⟨K', s.map (.subtype _), by rwa [← card_map] at hcards, fun p' hp' v hv w hw ↦ ?_⟩
    obtain ⟨w', hw'_mem, (hw'_eq : ↑w' = w)⟩ := Finset.mem_map.mp hw
    simp_rw [K', univ_eq_attach, Finset.mem_map, mem_attach,
      Function.Embedding.coeFn_mk, true_and, Subtype.exists] at hp'
    obtain ⟨p, hp, hp'_eq⟩ : ∃ p, ∃ (h : p ∈ K.parts), y p h = p' := hp'
    apply hs_subset at hw'_mem
    simp_rw [mem_filter, mem_univ, true_and, ErdosStone.filter.pi, Subtype.mk.injEq] at hw'_mem
    rw [← hp'_eq, mem_coe, ← hw'_mem] at hv
    rw [← hw'_eq]
    exact (ErdosStone.filter.pi.mem_val K hp w' v hv).symm

end ErdosStone

end SimpleGraph
