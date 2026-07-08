/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Complete Multipartite Graphs

A graph is complete multipartite iff non-adjacency is transitive.

## Main declarations

* `SimpleGraph.IsCompleteMultipartite`: predicate for a graph to be complete multipartite.

* `SimpleGraph.IsCompleteMultipartite.setoid`: the `Setoid` given by non-adjacency.

* `SimpleGraph.IsCompleteMultipartite.iso`: the graph isomorphism from a graph that
  `IsCompleteMultipartite` to the corresponding `completeMultipartiteGraph`.

* `SimpleGraph.IsPathGraph3Compl`: predicate for three vertices to witness the
  non-complete-multipartiteness of a graph `G`. (The name refers to the fact that the three
  vertices form the complement of `pathGraph 3`.)

* See also: `Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`.
  The lemma `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree` states that a maximally
  `r + 1`-cliquefree graph is `r`-colorable iff it is complete multipartite.

* `SimpleGraph.completeEquipartiteGraph`: the **complete equipartite graph** in parts of *equal*
  size such that two vertices are adjacent if and only if they are in different parts.

* `SimpleGraph.CompleteEquipartiteSubgraph G r t` is a complete equipartite subgraph, that is,
  `r` subsets of vertices each of size `t` such that the vertices in distinct subsets are
  adjacent.

## Implementation Notes

The definition of `completeEquipartiteGraph` is similar to `completeMultipartiteGraph`
except that `Sigma.fst` is replaced by `Prod.fst` in the definition. The difference is that the
former vertices are a product type whereas the latter vertices are a *dependent* product type.

While `completeEquipartiteGraph r t` could have been defined as the specialisation
`completeMultipartiteGraph (const (Fin r) (Fin t))` (or `turanGraph (r * t) r`), it is convenient
to instead have a *non-dependent* *product* type for the vertices.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`
for the isomorphisms between a `completeEquipartiteGraph` and a corresponding
`completeMultipartiteGraph`, `turanGraph`.
-/

@[expose] public section

open Finset Fintype Function

universe u
namespace SimpleGraph
variable {α : Type u} {G : SimpleGraph α} {s : Set α}

/-- `G` is `IsCompleteMultipartite` iff non-adjacency is transitive -/
def IsCompleteMultipartite (G : SimpleGraph α) : Prop := IsTrans α (¬ G.Adj · ·)

theorem bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite :=
  ⟨by simp⟩

protected lemma IsCompleteMultipartite.induce (hG : G.IsCompleteMultipartite) :
    (G.induce s).IsCompleteMultipartite where trans _u _v _w := hG.trans _ _ _

/-- The setoid given by non-adjacency -/
@[instance_reducible]
def IsCompleteMultipartite.setoid (h : G.IsCompleteMultipartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless.irrefl, fun h' ↦ by rwa [adj_comm] at h', h.trans _ _ _⟩⟩

lemma completeMultipartiteGraph.isCompleteMultipartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompleteMultipartite :=
  ⟨by simp_all⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The graph isomorphism from a graph `G` that `IsCompleteMultipartite` to the corresponding
`completeMultipartiteGraph` (see also `isCompleteMultipartite_iff`) -/
def IsCompleteMultipartite.iso (h : G.IsCompleteMultipartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) ↦ {x // h.setoid.r c.out x}) where
  toFun := fun x ↦ ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ ↦ x.1
  right_inv := fun ⟨_, x⟩ ↦ Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros
    change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

lemma isCompleteMultipartite_iff : G.IsCompleteMultipartite ↔ ∃ (ι : Type u) (V : ι → Type u)
    (_ : ∀ i, Nonempty (V i)), Nonempty (G ≃g completeMultipartiteGraph V) := by
  constructor <;> intro h
  · exact ⟨_, _, fun _ ↦ ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    refine ⟨fun _ _ _ h1 h2 ↦ ?_⟩
    rw [← e.map_rel_iff] at *
    exact completeMultipartiteGraph.isCompleteMultipartite _ |>.trans _ _ _ h1 h2

lemma IsCompleteMultipartite.colorable_of_cliqueFree {n : ℕ} (h : G.IsCompleteMultipartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) :=
  (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ ↦ ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.isContained).of_hom h.iso

variable (G) in
/--
The vertices `v, w₁, w₂` form an `IsPathGraph3Compl` in `G` iff `w₁w₂` is the only edge present
between these three vertices. It is a witness to the non-complete-multipartite-ness of `G` (see
`not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`). This structure is an explicit way of
saying that the induced graph on `{v, w₁, w₂}` is the complement of `P3`.
-/
structure IsPathGraph3Compl (v w₁ w₂ : α) : Prop where
  adj : G.Adj w₁ w₂
  not_adj_fst : ¬ G.Adj v w₁
  not_adj_snd : ¬ G.Adj v w₂

namespace IsPathGraph3Compl

variable {v w₁ w₂ : α}

@[grind →]
lemma ne_fst (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₁ :=
  fun h ↦ h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind →]
lemma ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₂ :=
  fun h ↦ h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind →]
lemma fst_ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : w₁ ≠ w₂ := h2.adj.ne

@[symm] lemma symm (h : G.IsPathGraph3Compl v w₁ w₂) : G.IsPathGraph3Compl v w₂ w₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

end IsPathGraph3Compl

lemma exists_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite G) :
    ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ := by
  apply mt IsTrans.mk at h
  push Not at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩

lemma not_isCompleteMultipartite_iff_exists_isPathGraph3Compl :
    ¬ IsCompleteMultipartite G ↔ ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ :=
  ⟨fun h ↦ G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ ↦ fun h ↦ h.trans _ _ _ (by rwa [adj_comm] at h2) h3 h1⟩

/--
Any `IsPathGraph3Compl` in `G` gives rise to a graph embedding of the complement of the path graph
-/
def IsPathGraph3Compl.pathGraph3ComplEmbedding {v w₁ w₂ : α} (h : G.IsPathGraph3Compl v w₁ w₂) :
    (pathGraph 3)ᶜ ↪g G where
  toFun := fun x ↦
    match x with
    | 0 => w₁
    | 1 => v
    | 2 => w₂
  inj' := by
    intro _ _ _
    have := h.ne_fst
    have := h.ne_snd
    have := h.adj.ne
    aesop
  map_rel_iff' := by
    intro _ _
    simp_rw [Embedding.coeFn_mk, compl_adj, ne_eq, pathGraph_adj, not_or]
    have := h.adj
    have := h.adj.symm
    have h1 := h.not_adj_fst
    have h2 := h.not_adj_snd
    have ⟨_, _⟩ : ¬ G.Adj w₁ v ∧ ¬ G.Adj w₂ v := by rw [adj_comm] at h1 h2; exact ⟨h1, h2⟩
    aesop

/-- Embedding of `(pathGraph 3)ᶜ` into `G` that is not complete-multipartite. -/
noncomputable def pathGraph3ComplEmbeddingOf (h : ¬ G.IsCompleteMultipartite) :
    (pathGraph 3)ᶜ ↪g G :=
  IsPathGraph3Compl.pathGraph3ComplEmbedding
    (exists_isPathGraph3Compl_of_not_isCompleteMultipartite h).choose_spec.choose_spec.choose_spec

lemma not_isCompleteMultipartite_of_pathGraph3ComplEmbedding (e : (pathGraph 3)ᶜ ↪g G) :
    ¬ IsCompleteMultipartite G := by
  intro h
  have h0 : ¬ G.Adj (e 0) (e 1) := by simp [pathGraph_adj]
  have h1 : ¬ G.Adj (e 1) (e 2) := by simp [pathGraph_adj]
  have h2 : G.Adj (e 0) (e 2) := by simp [pathGraph_adj]
  exact h.trans _ _ _ h0 h1 h2

theorem IsCompleteMultipartite.comap {β : Type*} {H : SimpleGraph β} (f : H ↪g G) :
    G.IsCompleteMultipartite → H.IsCompleteMultipartite := by
  intro h; contrapose h
  exact not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
          <| f.comp (pathGraph3ComplEmbeddingOf h)

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The **complete equipartite graph** in `r` parts each of *equal* size `t` such that two
vertices are adjacent if and only if they are in different parts, often denoted $K_r(t)$.

This is isomorphic to a corresponding `completeMultipartiteGraph` and `turanGraph`. The difference
is that the former vertices are a product type.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`. -/
abbrev completeEquipartiteGraph (r t : ℕ) : SimpleGraph (Fin r × Fin t) :=
  SimpleGraph.comap Prod.fst ⊤

lemma completeEquipartiteGraph_adj {v w} :
  (completeEquipartiteGraph r t).Adj v w ↔ v.1 ≠ w.1 := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are a
*dependent* product type. -/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (const (Fin r) (Fin t)) :=
  { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

set_option backward.isDefEq.respectTransparency.types false in
/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `turanGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are
not. -/
def completeEquipartiteGraph.turanGraph :
    completeEquipartiteGraph r t ≃g turanGraph (r * t) r where
  toFun := by
    refine fun v ↦ ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos, Nat.mul_add_one, mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v ↦ (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
    · have ⟨hr, _⟩ := CanonicallyOrderedAdd.mul_pos.mp v.pos
      exact Nat.mod_lt v hr
    · exact Nat.div_lt_of_lt_mul v.prop
  left_inv v := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · conv =>
        enter [1, 1, 1, 1, 1]
        rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt v.1.prop
    · apply le_antisymm
      · rw [Nat.div_le_iff_le_mul_add_pred v.1.pos, mul_comm r ↑v.2]
        exact Nat.add_le_add_left (Nat.le_pred_of_lt v.1.prop) (↑v.2 * r)
      · rw [Nat.le_div_iff_mul_le v.1.pos]
        exact Nat.le_add_right (↑v.2 * r) ↑v.1
  right_inv v := Fin.ext (Nat.div_add_mod' v r)
  map_rel_iff' {v w} := by
    rw [turanGraph_adj, Equiv.coe_fn_mk, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v.1.prop,
      Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt w.1.prop, ← Fin.ext_iff.ne,
      ← completeEquipartiteGraph_adj]

/-- `completeEquipartiteGraph r t` contains no edges when `r ≤ 1` or `t = 0`. -/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph r t = ⊥ ↔ r ≤ 1 ∨ t = 0 := by
  contrapose!
  rw [← edgeSet_nonempty, ← Nat.succ_le_iff, ← Fin.nontrivial_iff_two_le, ← Nat.pos_iff_ne_zero,
    Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ ↦ ?_⟩
  · induction e with | _ v₁ v₂
    rw [mem_edgeSet, completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet, completeEquipartiteGraph_adj]
    exact hv

theorem completeEquipartiteGraph.isCompleteMultipartite :
    (completeEquipartiteGraph r t).IsCompleteMultipartite := by
  rcases t.eq_zero_or_pos with ht_eq0 | ht_pos
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr (Or.inr ht_eq0)]
    exact bot_isCompleteMultipartite
  · rw [isCompleteMultipartite_iff]
    use (Fin r), const (Fin r) (Fin t)
    simp_rw [const_apply, exists_prop]
    exact ⟨const (Fin r) (Fin.pos_iff_nonempty.mp ht_pos),
      ⟨completeEquipartiteGraph.completeMultipartiteGraph⟩⟩

theorem neighborSet_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

theorem neighborFinset_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]

theorem degree_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).degree v = (r - 1) * t := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeEquipartiteGraph v,
    card_product, card_compl, card_singleton, Fintype.card_fin, card_univ, Fintype.card_fin]

theorem card_edgeFinset_completeEquipartiteGraph :
    #(completeEquipartiteGraph r t).edgeFinset = r.choose 2 * t ^ 2 := by
  rw [← mul_right_inj' two_ne_zero, ← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const, smul_eq_mul, card_univ, card_prod, Fintype.card_fin, Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc, Nat.choose_two_right, Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc, mul_comm r _, mul_assoc t _ _, mul_comm t, mul_assoc _ t, ← pow_two]

variable [Fintype α]

/-- Every `n`-colorable graph is contained in a `completeEquipartiteGraph` in `n` parts (as long
  as the parts are at least as large as the largest color class). -/
theorem isContained_completeEquipartiteGraph_of_colorable {n : ℕ} (C : G.Coloring (Fin n))
    (t : ℕ) (h : ∀ c, card (C.colorClass c) ≤ t) : G ⊑ completeEquipartiteGraph n t := by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le, Fintype.card_fin]
    exact h c
  have F (c : Fin n) := Classical.arbitrary (C.colorClass c ↪ Fin t)
  have hF {c₁ c₂ v₁ v₂} (hc : c₁ = c₂) (hv : F c₁ v₁ = F c₂ v₂) : v₁.val = v₂.val := by
    let v₁' : C.colorClass c₂ := ⟨v₁, by simp [← hc]⟩
    have hv' : F c₁ v₁ = F c₂ v₁' := by
      apply congr_heq
      · rw [hc]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc]
    rw [hv'] at hv
    simpa [Subtype.ext_iff] using (F c₂).injective hv
  use ⟨fun v ↦ (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro v w h
  rw [Prod.mk.injEq] at h
  exact hF h.1 h.2

end CompleteEquipartiteGraph

section CompleteEquipartiteSubgraph

variable {V : Type*} {G : SimpleGraph V}

/-- A complete equipartite subgraph in `r > 0` parts each of size `t ≠ 0` in `G` is `r` subsets
of vertices each of size `t` such that vertices in distinct subsets are adjacent.

If `r > 0` but `t = 0`, then `parts = {{}}`. If `r = 0`, then `parts = {}`. These are the two
*distinct* "empty" complete equipartite subgraphs, that is, the complete equipartite subgraphs
having no vertices. -/
@[ext]
structure CompleteEquipartiteSubgraph (G : SimpleGraph V) (r t : ℕ) where
  /-- The parts in a complete equipartite subgraph. -/
  parts : Finset (Finset V)
  /-- There are `r` parts or `t = 0`. -/
  card_parts : #parts = r ∨ t = 0
  /-- There are `t` vertices in each part. -/
  card_mem_parts {p} : p ∈ parts → #p = t
  /-- The vertices in distinct parts are adjacent. -/
  isCompleteBetween : (parts : Set (Finset V)).Pairwise (G.IsCompleteBetween · ·)

variable {r t : ℕ} (K : G.CompleteEquipartiteSubgraph r t)

namespace CompleteEquipartiteSubgraph

/-- At least one of the "empty" complete equipartite subgraphs is contained in a simple graph. -/
theorem nonempty_of_eq_zero_or_eq_zero (h : r = 0 ∨ t = 0) :
    Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨{}, h.elim (fun hr ↦ by simp [hr]) (fun ht ↦ by simp [ht]), by simp, by simp⟩

/-- The parts in a complete equipartite subgraph are pairwise disjoint. -/
theorem disjoint : (K.parts : Set (Finset V)).Pairwise Disjoint :=
  fun _ h₁ _ h₂ hne ↦ Finset.disjoint_left.mpr fun _ h₁' h₂' ↦
    G.irrefl <| K.isCompleteBetween h₁ h₂ hne h₁' h₂'

/-- The finset of vertices in a complete equipartite subgraph. -/
def verts : Finset V := K.parts.disjiUnion id K.disjoint

open scoped Classical in
/-- The finset of vertices in a complete equipartite subgraph as a `biUnion`. -/
lemma verts_eq_biUnion : K.verts = K.parts.biUnion id := by rw [verts, disjiUnion_eq_biUnion]

set_option backward.isDefEq.respectTransparency.types false in
/-- There are `r * t` vertices in a complete equipartite subgraph with `r` parts of size `t`. -/
theorem card_verts : #K.verts = r * t := by
  simp_rw [verts, card_disjiUnion, id_eq, sum_congr rfl fun _ ↦ K.card_mem_parts, sum_const,
    smul_eq_mul, mul_eq_mul_right_iff]
  exact K.card_parts

/-- A complete equipartite subgraph gives rise to a copy of a complete equipartite graph. -/
noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  by_cases ht : t = 0
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht]
    have : IsEmpty (Fin r × Fin t) := by simp [ht, Fin.isEmpty]
    exact Copy.bot .ofIsEmpty
  · have : Nonempty (Fin r ↪ K.parts) := by
      rw [Embedding.nonempty_iff_card_le,
        Fintype.card_fin, card_coe, K.card_parts.resolve_right ht]
    let fᵣ : Fin r ↪ K.parts := Classical.arbitrary (Fin r ↪ K.parts)
    have (p : K.parts) : Nonempty (Fin t ↪ p) := by
      rw [Embedding.nonempty_iff_card_le, Fintype.card_fin, card_coe, K.card_mem_parts p.prop]
    let fₜ (p : K.parts) : Fin t ↪ p :=
      Classical.arbitrary (Fin t ↪ p)
    let f : (Fin r) × (Fin t) ↪ V := by
      use fun (i, j) ↦ fₜ (fᵣ i) j
      intro (i₁, j₁) (i₂, j₂) heq
      rw [Prod.mk.injEq]
      contrapose! heq with hne
      rcases eq_or_ne i₁ i₂ with heq | hne
      · rw [heq, ← Subtype.ext_iff.ne]
        exact (fₜ _).injective.ne (hne heq)
      · refine (K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop).ne
        exact Subtype.ext_iff.ne.mp <| fᵣ.injective.ne hne
    refine ⟨⟨f, fun hne ↦ ?_⟩, f.injective⟩
    refine K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop
    exact Subtype.ext_iff.ne.mp <| fᵣ.injective.ne hne

set_option backward.isDefEq.respectTransparency.types false in
/-- A copy of a complete equipartite graph identifies a complete equipartite subgraph. -/
def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartiteSubgraph r t := by
  by_cases ht : t = 0
  · exact ⟨∅, .inr ht, by simp, by simp⟩
  · refine ⟨univ.map ⟨fun i ↦ univ.map ⟨fun j ↦ f (i, j), fun _ _ h ↦ ?_⟩, fun i₁ i₂ h ↦ ?_⟩,
      ?_, fun h ↦ ?_, fun _ h₁ _ h₂ hne _ h₁' _ h₂' ↦ ?_⟩
    · simpa using f.injective h
    · simp_rw [Finset.ext_iff] at h
      have : NeZero t := ⟨ht⟩
      obtain ⟨_, heq⟩ : ∃ j, f (i₁, j) = f (i₂, 0) := by simpa using h <| f (i₂, 0)
      apply f.injective at heq
      rw [Prod.mk.injEq] at heq
      exact heq.left
    · simp
    · simp_rw [mem_map, mem_univ, Embedding.coeFn_mk, true_and] at h
      replace ⟨_, h⟩ := h
      simp [← h]
    · simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁ h₂
      replace ⟨_, h₁⟩ := h₁
      replace ⟨_, h₂⟩ := h₂
      rw [← h₁] at h₁'
      rw [← h₂] at h₂'
      simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁' h₂'
      replace ⟨_, h₁'⟩ := h₁'
      replace ⟨_, h₂'⟩ := h₂'
      rw [← h₁', ← h₂']
      apply f.toHom.map_adj
      simp_rw [completeEquipartiteGraph_adj]
      contrapose hne with heq
      simp_rw [← h₁, ← h₂, heq]

end CompleteEquipartiteSubgraph

/-- Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type
`G.CompleteEquipartiteSubgraph r t` is nonempty. -/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ ↦ ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ ↦ ⟨K.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (r + 1) t` iff there exists
`s : Finset V` of size `#s = t` and `K : G.CompleteEquipartiteSubgraph r t` such that the
vertices in `s` are adjacent to the vertices in `K`. -/
theorem completeEquipartiteGraph_succ_isContained_iff :
  completeEquipartiteGraph (r + 1) t ⊑ G
    ↔ ∃ᵉ (K : G.CompleteEquipartiteSubgraph r t) (s : Finset V),
        #s = t ∧ ∀ p ∈ K.parts, G.IsCompleteBetween p s := by
  classical
  by_cases ht : t = 0
  · have (r' : ℕ) : IsEmpty (Fin r' × Fin t) := by simp [ht, Fin.isEmpty]
    have h_bot (r' : ℕ) : completeEquipartiteGraph r' t = ⊥ :=
      completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht
    simp_rw [h_bot (r + 1), ht, Finset.card_eq_zero, exists_eq_left, IsCompleteBetween, mem_coe,
      notMem_empty, IsEmpty.forall_iff, implies_true, exists_true_iff_nonempty]
    exact ⟨fun _ ↦ CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero (.inr ht),
      fun _ ↦ ⟨Copy.bot .ofIsEmpty⟩⟩
  · rw [completeEquipartiteGraph_isContained_iff]
    refine ⟨fun ⟨K'⟩ ↦ ?_, fun ⟨K, s, hs, hadj⟩ ↦ ?_⟩
    · obtain ⟨parts, hparts_sub, hparts_card⟩ := K'.parts.exists_subset_card_eq (Nat.pred_le _)
      let K : G.CompleteEquipartiteSubgraph r t := by
        refine ⟨parts, ?_, fun h ↦ K'.card_mem_parts (hparts_sub h),
          fun _ h₁ _ h₂ hne ↦ K'.isCompleteBetween (hparts_sub h₁) (hparts_sub h₂) hne⟩
        rw [hparts_card, K'.card_parts.resolve_right ht]
        exact .inl (Nat.pred_succ r)
      obtain ⟨s, nhs_mem, hs⟩ : ∃ s ∉ K.parts, insert s K.parts = K'.parts := by
        refine exists_eq_insert_iff.mpr ⟨hparts_sub, ?_⟩
        rw [K.card_parts.resolve_right ht, K'.card_parts.resolve_right ht]
      have hs_mem : s ∈ K'.parts := by simp [← hs]
      exact ⟨K, s, K'.card_mem_parts hs_mem,
        fun _ h ↦ K'.isCompleteBetween (hparts_sub h) hs_mem (ne_of_mem_of_not_mem h nhs_mem)⟩
    · refine ⟨K.parts.cons s ?_, ?_, ?_, ?_⟩
      · intro hs_mem
        obtain ⟨v, hv⟩ : s.Nonempty := by
          rw [← Finset.card_pos, hs]
          exact Nat.pos_of_ne_zero ht
        exact G.irrefl <| hadj s hs_mem hv hv
      · rw [Finset.card_cons, K.card_parts.resolve_right ht]
        exact .inl rfl
      · simp_rw [mem_cons, forall_eq_or_imp]
        exact ⟨hs, fun p ↦ K.card_mem_parts⟩
      · rw [coe_cons]
        have : Std.Symm G.IsCompleteBetween := by simp [symm_def, isCompleteBetween_comm]
        exact K.isCompleteBetween.insert_of_symm fun p hp _ ↦ hadj p hp |>.symm

end CompleteEquipartiteSubgraph

end SimpleGraph
