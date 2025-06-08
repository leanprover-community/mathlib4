/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Data.Real.Basic
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

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {s t u : Finset α}

namespace SimpleGraph

/-- The vertices of `s` whose density in `t` is `ε` less than expected. -/
private noncomputable def badVertices (ε : ℝ) (s t : Finset α) : Finset α :=
  {x ∈ s | #{y ∈ t | G.Adj x y} < (G.edgeDensity s t - ε) * #t}

private lemma card_interedges_badVertices_le :
    #(Rel.interedges G.Adj (badVertices G ε s t) t) ≤
      #(badVertices G ε s t) * #t * (G.edgeDensity s t - ε) := by
  classical
  refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (#t : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le

private lemma edgeDensity_badVertices_le (hε : 0 ≤ ε) (dst : 2 * ε ≤ G.edgeDensity s t) :
    G.edgeDensity (badVertices G ε s t) t ≤ G.edgeDensity s t - ε := by
  rw [edgeDensity_def]
  push_cast
  refine div_le_of_le_mul₀ (by positivity) (sub_nonneg_of_le <| by linarith) ?_
  rw [mul_comm]
  exact G.card_interedges_badVertices_le

private lemma card_badVertices_le (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t) :
    #(badVertices G ε s t) ≤ #s * ε := by
  have hε : ε ≤ 1 := (le_rfl.trans <| le_mul_of_one_le_left hst.pos.le (by norm_num)).trans
    (dst.trans <| by exact_mod_cast edgeDensity_le_one _ _ _)
  by_contra! h
  have : |(G.edgeDensity (badVertices G ε s t) t - G.edgeDensity s t : ℝ)| < ε :=
    hst (filter_subset _ _) Subset.rfl h.le (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)
  rw [abs_sub_lt_iff] at this
  linarith [G.edgeDensity_badVertices_le hst.pos.le dst]

/-- A subset of the triangles constructed in a weird way to make them easy to count. -/
private lemma triangle_split_helper [DecidableEq α] :
    (s \ (badVertices G ε s t ∪ badVertices G ε s u)).biUnion
      (fun x ↦ (G.interedges {y ∈ t | G.Adj x y} {y ∈ u | G.Adj x y}).image (x, ·)) ⊆
      (s ×ˢ t ×ˢ u).filter (fun (x, y, z) ↦ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
  rintro ⟨x, y, z⟩
  simp only [mem_filter, mem_product, mem_biUnion, mem_sdiff, exists_prop, mem_union,
    mem_image, Prod.exists, and_assoc, exists_imp, and_imp, Prod.mk_inj, mem_interedges_iff]
  rintro x hx - y z hy xy hz xz yz rfl rfl rfl
  exact ⟨hx, hy, hz, xy, xz, yz⟩

private lemma good_vertices_triangle_card [DecidableEq α] (dst : 2 * ε ≤ G.edgeDensity s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u)
    (x : α) (hx : x ∈ s \ (badVertices G ε s t ∪ badVertices G ε s u)) :
    ε ^ 3 * #t * #u ≤ #((({y ∈ t | G.Adj x y} ×ˢ {y ∈ u | G.Adj x y}).filter
        fun (y, z) ↦ G.Adj y z).image (x, ·)) := by
  simp only [mem_sdiff, badVertices, mem_union, not_or, mem_filter, not_and_or, not_lt] at hx
  rw [← or_and_left, and_or_left] at hx
  simp only [false_or, and_not_self, mul_comm (_ - _)] at hx
  obtain ⟨-, hxY, hsu⟩ := hx
  have hY : #t * ε ≤ #{y ∈ t | G.Adj x y} := by
    refine le_trans ?_ hxY; gcongr; linarith
  have hZ : #u * ε ≤ #{y ∈ u | G.Adj x y} := by
    refine le_trans ?_ hsu; gcongr; linarith
  rw [card_image_of_injective _ (Prod.mk_right_injective _)]
  have := utu (filter_subset (G.Adj x) _) (filter_subset (G.Adj x) _) hY hZ
  have : ε ≤ G.edgeDensity {y ∈ t | G.Adj x y} {y ∈ u | G.Adj x y} := by
    rw [abs_sub_lt_iff] at this; linarith
  rw [edgeDensity_def] at this
  push_cast at this
  have hε := utu.pos.le
  refine le_trans ?_ (mul_le_of_le_div₀ (Nat.cast_nonneg _) (by positivity) this)
  refine Eq.trans_le ?_
    (mul_le_mul_of_nonneg_left (mul_le_mul hY hZ (by positivity) (by positivity)) hε)
  ring

/-- The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are sets of vertices such
that each pair is `ε`-uniform and `2 * ε`-dense, then a proportion of at least
`(1 - 2 * ε) * ε ^ 3` of the triples `(a, b, c) ∈ s × t × u` are triangles. -/
lemma triangle_counting'
    (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) :
    (1 - 2 * ε) * ε ^ 3 * #s * #t * #u ≤
      #((s ×ˢ t ×ˢ u).filter fun (a, b, c) ↦ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := by
  classical
  have h₁ : #(badVertices G ε s t) ≤ #s * ε := G.card_badVertices_le dst hst
  have h₂ : #(badVertices G ε s u) ≤ #s * ε := G.card_badVertices_le dsu usu
  let X' := s \ (badVertices G ε s t ∪ badVertices G ε s u)
  have : X'.biUnion _ ⊆ (s ×ˢ t ×ˢ u).filter fun (a, b, c) ↦ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
    triangle_split_helper _
  refine le_trans ?_ (Nat.cast_le.2 <| card_le_card this)
  rw [card_biUnion, Nat.cast_sum]
  · apply le_trans _ (card_nsmul_le_sum X' _ _ <| G.good_vertices_triangle_card dst dsu dtu utu)
    rw [nsmul_eq_mul]
    have := hst.pos.le
    suffices hX' : (1 - 2 * ε) * #s ≤ #X' by
      exact Eq.trans_le (by ring) (mul_le_mul_of_nonneg_right hX' <| by positivity)
    have i : badVertices G ε s t ∪ badVertices G ε s u ⊆ s :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    rw [sub_mul, one_mul, card_sdiff i, Nat.cast_sub (card_le_card i), sub_le_sub_iff_left,
      mul_assoc, mul_comm ε, two_mul]
    refine (Nat.cast_le.2 <| card_union_le _ _).trans ?_
    rw [Nat.cast_add]
    gcongr
  rintro a _ b _ t
  rw [Function.onFun, disjoint_left]
  simp only [Prod.forall, mem_image, not_exists, exists_prop, mem_filter, Prod.mk_inj,
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
  rw [Prod.mk_inj, Prod.mk_inj]
  simp only [and_assoc, @or_left_comm _ (y₁ = y₂), @or_comm _ (z₁ = z₂),
    @or_left_comm _ (z₁ = z₂)] at h
  refine ⟨h.1.resolve_right (not_or_intro ?_ ?_), h.2.1.resolve_right (not_or_intro ?_ ?_),
    h.2.2.1.resolve_right (not_or_intro ?_ ?_)⟩ <;>
  · rintro rfl
    solve_by_elim

variable [Fintype α]

/-- The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are disjoint sets of
vertices such that each pair is `ε`-uniform and `2 * ε`-dense, then `G` contains at least
`(1 - 2 * ε) * ε ^ 3 * |s| * |t| * |u|` triangles. -/
lemma triangle_counting
    (dst : 2 * ε ≤ G.edgeDensity s t) (ust : G.IsUniform ε s t) (hst : Disjoint s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u) (hsu : Disjoint s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) (htu : Disjoint t u) :
    (1 - 2 * ε) * ε ^ 3 * #s * #t * #u ≤ #(G.cliqueFinset 3) := by
  apply (G.triangle_counting' dst ust dsu usu dtu utu).trans _
  rw [Nat.cast_le]
  refine card_le_card_of_injOn (fun (x, y, z) ↦ {x, y, z}) ?_ ?_
  · rintro ⟨x, y, z⟩
    simp only [and_imp, mem_filter, mem_product, mem_cliqueFinset_iff, is3Clique_triple_iff]
    exact fun _ _ _ hxy hxz hyz ↦ ⟨hxy, hxz, hyz⟩
  rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ t
  simp only [mem_coe, mem_filter, mem_product] at h₁ h₂
  apply triple_eq_triple_of_mem hst hsu htu t <;> tauto

end SimpleGraph
