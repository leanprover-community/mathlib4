/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Partition.Equipartition
import Mathlib.Tactic.Linarith

/-!
# Triangle counting lemma

In this file, we prove the triangle counting lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

-- TODO: This instance is bad because it creates data out of a Prop
attribute [-instance] decidableEq_of_subsingleton

open Finset Fintype
open scoped BigOperators

variable {α : Type*} (G G' : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {s t u : Finset α}

namespace SimpleGraph

/-- The pairs of vertices whose density is big. -/
private noncomputable def badVertices (ε : ℝ) (s t : Finset α) :=
  s.filter fun x ↦ ((t.filter $ G.Adj x).card : ℝ) < (G.edgeDensity s t - ε) * t.card

private lemma interedges_badVertices [DecidableEq α] :
    Rel.interedges G.Adj (badVertices G ε s t) t =
      (badVertices G ε s t).biUnion (fun x ↦ (t.filter (G.Adj x)).image (x, ·)) := by
  ext ⟨x, y⟩
  simp only [mem_biUnion, mem_image, exists_prop, mem_filter, Prod.mk.inj_iff,
    exists_eq_right_right, Rel.mem_interedges_iff]

private lemma pairs_card_bad_le :
    ((Rel.interedges G.Adj (badVertices G ε s t) t).card : ℝ) ≤
      (badVertices G ε s t).card * t.card * (G.edgeDensity s t - ε) := by
  classical
  refine (Nat.cast_le.2 $ (card_le_of_subset $ subset_of_eq G.interedges_badVertices).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_image_of_injective _ (Prod.mk.inj_left _), ←nsmul_eq_mul,
    smul_mul_assoc, mul_comm (t.card : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le

private lemma edgeDensity_badVertices (hε : 0 ≤ ε) (dst : 2 * ε ≤ G.edgeDensity s t) :
    (G.edgeDensity (badVertices G ε s t) t : ℝ) ≤ G.edgeDensity s t - ε := by
  rw [edgeDensity_def]
  push_cast
  refine div_le_of_nonneg_of_le_mul (by positivity) (sub_nonneg_of_le $ by linarith) ?_
  rw [mul_comm]
  exact G.pairs_card_bad_le

private lemma few_badVertices (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t) :
  ((badVertices G ε s t).card : ℝ) ≤ s.card * ε := by
  have hε : ε ≤ 1 := (le_mul_of_one_le_of_le_of_nonneg (by norm_num) le_rfl hst.pos.le).trans
    (dst.trans $ by exact_mod_cast edgeDensity_le_one _ _ _)
  by_contra! h
  have : |(G.edgeDensity (badVertices G ε s t) t : ℝ) - G.edgeDensity s t| < ε :=
    hst (filter_subset _ _) Subset.rfl h.le (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)
  rw [abs_sub_lt_iff] at this
  linarith [G.edgeDensity_badVertices hst.pos.le dst]

/-- A subset of the triangles constructed in a weird way to make them easy to count. -/
private lemma triangle_split_helper [DecidableEq α] :
  (s \ (badVertices G ε s t ∪ badVertices G ε s u)).biUnion
    (fun x ↦ ((t.filter (G.Adj x) ×ˢ u.filter (G.Adj x)).filter
      (fun (y, z) ↦ G.Adj y z)).image (x, ·)) ⊆
    (s ×ˢ t ×ˢ u).filter (fun (x, y, z) ↦ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
  rintro ⟨x, y, z⟩
  simp only [mem_filter, mem_product, mem_biUnion, mem_sdiff, exists_prop, mem_union,
    mem_image, Prod.exists, and_assoc, exists_imp, and_imp, Prod.mk.inj_iff]
  rintro x hx - y z hy xy hz xz yz rfl rfl rfl
  exact ⟨hx, hy, hz, xy, xz, yz⟩

private lemma good_vertices_triangle_card [DecidableEq α] (dst : 2 * ε ≤ G.edgeDensity s t)
  (dsu : 2 * ε ≤ G.edgeDensity s u) (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u)
  (x : α) (hx : x ∈ s \ (badVertices G ε s t ∪ badVertices G ε s u)) :
  ε^3 * t.card * u.card ≤ (((t.filter (G.Adj x) ×ˢ u.filter (G.Adj x)).filter
      (fun (y, z) ↦ G.Adj y z)).image (x, ·)).card := by
  simp only [mem_sdiff, badVertices, mem_union, not_or, mem_filter, not_and_or, not_lt] at hx
  rw [←or_and_left, and_or_left] at hx
  simp only [false_or, and_not_self, mul_comm ((_ : ℝ) - _)] at hx
  obtain ⟨-, hxY, hsu⟩ := hx
  have hY : (t.card : ℝ) * ε ≤ (filter (G.Adj x) t).card
  { exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)).trans hxY }
  have hZ : (u.card : ℝ) * ε ≤ (filter (G.Adj x) u).card
  { exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)).trans hsu }
  rw [card_image_of_injective _ (Prod.mk.inj_left _)]
  have := utu (filter_subset (G.Adj x) _) (filter_subset (G.Adj x) _) hY hZ
  have : ε ≤ G.edgeDensity (filter (G.Adj x) t) (filter (G.Adj x) u)
  · rw [abs_sub_lt_iff] at this
    linarith
  rw [edgeDensity_def] at this
  push_cast at this
  have hε := utu.pos.le
  refine le_trans ?_ (mul_le_of_nonneg_of_le_div (Nat.cast_nonneg _) (by positivity) this)
  refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left (mul_le_mul hY hZ (by positivity) $
    by positivity) hε)
  ring

lemma triangle_counting
  (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t)
  (dsu : 2 * ε ≤ G.edgeDensity s u) (uXZ : G.IsUniform ε s u)
  (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) :
  (1 - 2 * ε) * ε^3 * s.card * t.card * u.card ≤
    ((s ×ˢ t ×ˢ u).filter fun (x, y, z) ↦ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z).card := by
  classical
  have h₁ : ((badVertices G ε s t).card : ℝ) ≤ s.card * ε := G.few_badVertices dst hst
  have h₂ : ((badVertices G ε s u).card : ℝ) ≤ s.card * ε := G.few_badVertices dsu uXZ
  let X' := s \ (badVertices G ε s t ∪ badVertices G ε s u)
  have : X'.biUnion _ ⊆ (s ×ˢ t ×ˢ u).filter fun (x, y, z) ↦ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z
  · apply triangle_split_helper
  refine le_trans ?_ (Nat.cast_le.2 $ card_le_of_subset this)
  rw [card_biUnion, Nat.cast_sum]
  · apply le_trans _ (card_nsmul_le_sum X' _ _ $ G.good_vertices_triangle_card dst dsu dtu utu)
    rw [nsmul_eq_mul]
    have := hst.pos.le
    suffices hX' : (1 - 2 * ε) * s.card ≤ X'.card
    · exact Eq.trans_le (by ring) (mul_le_mul_of_nonneg_right hX' $ by positivity)
    have i : badVertices G ε s t ∪ badVertices G ε s u ⊆ s
    · apply union_subset (filter_subset _ _) (filter_subset _ _)
    rw [sub_mul, one_mul, card_sdiff i, Nat.cast_sub (card_le_of_subset i), sub_le_sub_iff_left,
      mul_assoc, mul_comm ε, two_mul]
    refine (Nat.cast_le.2 $ card_union_le _ _).trans ?_
    rw [Nat.cast_add]
    exact add_le_add h₁ h₂
  rintro x hx y hy t
  rw [disjoint_left]
  simp only [Prod.forall, mem_image, not_exists, exists_prop, mem_filter, Prod.mk.inj_iff,
    exists_imp, and_imp, not_and, mem_product, or_assoc]
  aesop

variable [DecidableEq α]

private lemma triple_eq_triple_of_mem (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
  {x₁ x₂ y₁ y₂ z₁ z₂ : α} (h : ({x₁, y₁, z₁} : Finset α) = {x₂, y₂, z₂})
  (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s) (hy₁ : y₁ ∈ t) (hy₂ : y₂ ∈ t) (hz₁ : z₁ ∈ u) (hz₂ : z₂ ∈ u) :
  (x₁, y₁, z₁) = (x₂, y₂, z₂) := by
  simp only [Finset.Subset.antisymm_iff, subset_iff, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq] at h
  rw [disjoint_left] at hst hsu htu
  rw [Prod.mk.inj_iff, Prod.mk.inj_iff]
  simp only [and_assoc, @or_left_comm _ (y₁ = y₂), @or_comm _ (z₁ = z₂),
    @or_left_comm _ (z₁ = z₂)] at h
  refine ⟨h.1.resolve_right (not_or_intro ?_ ?_), h.2.1.resolve_right (not_or_intro ?_ ?_),
    h.2.2.1.resolve_right (not_or_intro ?_ ?_)⟩ <;>
  · rintro rfl
    solve_by_elim

variable [Fintype α] {P : Finpartition (univ : Finset α)}

lemma triangle_counting2
    (dst : 2 * ε ≤ G.edgeDensity s t) (ust : G.IsUniform ε s t) (hst : Disjoint s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (uXZ : G.IsUniform ε s u) (hsu : Disjoint s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) (htu : Disjoint t u) :
    (1 - 2 * ε) * ε^3 * s.card * t.card * u.card ≤ (G.cliqueFinset 3).card := by
  apply (G.triangle_counting dst ust dsu uXZ dtu utu).trans _
  rw [Nat.cast_le]
  refine card_le_card_of_inj_on (fun (x, y, z) ↦ {x, y, z}) ?_ ?_
  · rintro ⟨x, y, z⟩
    simp only [and_imp, mem_filter, mem_product, mem_cliqueFinset_iff, is3Clique_triple_iff]
    exact fun _ _ _ hxy hxz hyz ↦ ⟨hxy, hxz, hyz⟩
  rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ t
  simp only [mem_filter, mem_product] at h₁ h₂
  apply triple_eq_triple_of_mem hst hsu htu t <;> tauto

variable {G G'}

lemma reduced_double_edges :
  univ.filter (fun (x, y) ↦ G.Adj x y) \
    univ.filter (fun (x, y) ↦ (G.reduced P (ε/8) (ε/4)).Adj x y) ⊆
      (P.nonUniforms G (ε/8)).biUnion (fun (U, V) ↦ (U ×ˢ V)) ∪
        P.parts.biUnion offDiag ∪
          (P.parts.offDiag.filter fun (U, V) ↦ G.edgeDensity U V < ε/4).biUnion
            fun (U, V) ↦ (U ×ˢ V).filter fun (x, y) ↦ G.Adj x y := by
  rintro ⟨x, y⟩
  simp only [mem_sdiff, mem_filter, mem_univ, true_and, reduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, exists_prop, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms_iff]
  rw [mem_filter] -- TODO: Why does simp not use `mem_filter`
  simp only [mem_sdiff, mem_filter, mem_univ, true_and, reduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, exists_prop, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms_iff]
  intros h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem (mem_univ x)
  obtain ⟨V, hV, hy⟩ := P.exists_mem (mem_univ y)
  rcases eq_or_ne U V with rfl | hUV
  { exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩) }
  by_cases h₂ : G.IsUniform (ε/8) U V
  · exact Or.inr $ Or.inr ⟨U, V, hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂, hx, hy, h⟩
  · exact Or.inl ⟨U, V, hU, hV, hUV, h₂, hx, hy⟩

lemma internal_killed_card (hP : P.IsEquipartition) :
    ((P.parts.biUnion offDiag).card : ℝ) ≤ card α * (card α + P.parts.card) / P.parts.card := by
  have : (P.parts.biUnion offDiag).card ≤
    P.parts.card * (card α / P.parts.card) * (card α / P.parts.card + 1)
  · rw [mul_assoc]
    refine card_biUnion_le_card_mul _ _ _ fun U hU ↦ ?_
    suffices : (U.card - 1) * U.card ≤ card α / P.parts.card * (card α / P.parts.card + 1)
    · rwa [Nat.mul_sub_right_distrib, one_mul, ←offDiag_card] at this
    have := hP.card_part_le_average_add_one hU
    refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
    simp only [Nat.add_succ_sub_one, add_zero, card_univ, le_rfl]
  refine (Nat.cast_le.2 this).trans ?_
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have i : (_ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (P.parts_nonempty univ_nonempty.ne_empty).card_pos.ne'
  rw [mul_div_assoc, div_add_same i, Nat.cast_mul, Nat.cast_add_one]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · rw [Nat.cast_le, mul_comm]
    exact Nat.div_mul_le_self _ _
  exact add_le_add_right Nat.cast_div_le _

lemma sparse_card (hP : P.IsEquipartition) (hε : 0 ≤ ε) :
  (((P.parts.offDiag.filter fun (U, V) ↦ G.edgeDensity U V < ε).biUnion $
      fun (U, V) ↦ G.interedges U V).card : ℝ) ≤
    ε * (card α + P.parts.card)^2 := by
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  rw [Nat.cast_sum]
  have : ∀ UV ∈ P.parts.offDiag.filter (fun (U, V) ↦ G.edgeDensity U V < ε),
    (G.interedges UV.1 UV.2).card ≤ ε * (UV.1.card * UV.2.card)
  · simp only [and_imp, mem_offDiag, mem_filter, Ne.def, SimpleGraph.edgeDensity_def]
    push_cast
    rintro ⟨U, V⟩ hU hV - e
    apply le_of_lt
    rwa [←div_lt_iff]
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hV).card_pos)
  apply (sum_le_sum this).trans
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ ↦ ?_).trans ?_
  · positivity
  rw [←mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hε
  refine (sum_le_card_nsmul P.parts.offDiag (fun i ↦ (i.1.card * i.2.card : ℝ))
    ((card α / P.parts.card + 1)^2 : ℕ) ?_).trans ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms_iff, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  rw [nsmul_eq_mul, ←Nat.cast_mul, ←Nat.cast_add, ←Nat.cast_pow, Nat.cast_le, offDiag_card,
    Nat.mul_sub_right_distrib, ←sq, ←mul_pow, mul_add_one]
  exact (Nat.sub_le _ _).trans
    (Nat.pow_le_pow_of_le_left (add_le_add_right (Nat.mul_div_le _ _) _) _)

private lemma aux {i j : ℕ} (hj : 0 < j) : j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2 := by
  have : j * (j - 1) < j^2
  · rw [sq]
    exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this $ pow_pos Nat.succ_pos' _).trans_le
  rw [←mul_pow]
  exact Nat.pow_le_pow_of_le_left (add_le_add_right (Nat.mul_div_le i j) _) _

lemma sum_nonUniforms_lt_of_isUniform [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    ((∑ i in P.nonUniforms G ε, i.1.card * i.2.card) : ℝ) < ε * (card α + P.parts.card)^2 := by
  refine (sum_le_card_nsmul (P.nonUniforms G ε) (fun i ↦ (i.1.card * i.2.card : ℝ))
    ((card α / P.parts.card + 1)^2 : ℕ) ?_).trans_lt ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms_iff, and_imp]
    rintro U V hU hV - -
    rw [sq, ←Nat.cast_mul, Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hG $ Nat.cast_nonneg _).trans_lt ?_
  rw [mul_right_comm _ ε, mul_comm ε]
  apply mul_lt_mul_of_pos_right _ hε
  norm_cast
  exact aux (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos

lemma sum_nonUniforms_lt_of_isUniform' [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    (((P.nonUniforms G ε).biUnion fun (U, V) ↦ U ×ˢ V).card : ℝ) < 4 * ε * (card α) ^ 2 := by
  calc
    _ ≤ ∑ i in P.nonUniforms G ε, (i.1.card * i.2.card : ℝ) := by
        norm_cast; simp_rw [←card_product]; exact card_biUnion_le
    _ < _ := sum_nonUniforms_lt_of_isUniform hε hP hG
    _ ≤ ε * (card α + card α) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

lemma sum_sparse (hε : 0 ≤ ε) (hP : P.IsEquipartition) :
    (((P.parts.offDiag.filter fun (U, V) ↦ G.edgeDensity U V < ε).biUnion $
            fun (U, V) ↦ (U ×ˢ V).filter fun (x, y) ↦ G.Adj x y).card : ℝ) ≤
              4 * ε * (card α)^2 := by
  refine (sparse_card hP hε).trans ?_
  suffices : ε * ((card α) + P.parts.card)^2 ≤ ε * (card α + card α)^2
  { exact this.trans_eq (by ring) }
  refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (by positivity) ?_ _) hε
  exact add_le_add_left (Nat.cast_le.2 P.card_parts_le_card) _

lemma internal_killed_card' (hε : 0 < ε) (hP : P.IsEquipartition) (hP' : 4 / ε ≤ P.parts.card) :
    ((P.parts.biUnion offDiag).card : ℝ) ≤ ε / 2 * (card α)^2 := by
  cases isEmpty_or_nonempty α
  { rw [Subsingleton.elim (P.parts.biUnion offDiag) ∅, Finset.card_empty, Nat.cast_zero]
    positivity }
  apply (internal_killed_card hP).trans
  rw [div_le_iff (Nat.cast_pos.2 (P.parts_nonempty univ_nonempty.ne_empty).card_pos)]
  have : (card α : ℝ) + P.parts.card ≤ 2 * card α
  · rw [two_mul]
    exact add_le_add_left (Nat.cast_le.2 P.card_parts_le_card) _
  refine (mul_le_mul_of_nonneg_left this $ by positivity).trans ?_
  suffices : 1 ≤ ε/4 * P.parts.card
  · rw [mul_left_comm, ←sq]
    convert mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two $ sq_nonneg (card α : ℝ))
      using 1 <;> ring
  rwa [←div_le_iff', one_div_div]
  positivity

end SimpleGraph
