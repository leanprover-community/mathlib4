/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Complete Multipartite Graphs

A graph is complete multipartite iff non-adjacency is transitive.

## Main declarations

* `SimpleGraph.IsCompleteMultipartite`: predicate for a graph to be complete-multi-partite.

* `SimpleGraph.IsCompleteMultipartite.setoid`: the `Setoid` given by non-adjacency.

* `SimpleGraph.IsCompleteMultipartite.iso`: the graph isomorphism from a graph that
  `IsCompleteMultipartite` to the corresponding `completeMultipartiteGraph`.

* `SimpleGraph.IsPathGraph3Compl`: predicate for three vertices to be a witness to
  non-complete-multi-partite-ness of a graph G. (The name refers to the fact that the three
  vertices form the complement of `pathGraph 3`.)

* See also: `Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`
  `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree` a maximally `r + 1`- cliquefree graph
  is `r`-colorable iff it is complete-multipartite.

* `SimpleGraph.completeEquipartiteGraph`: the **complete equipartite graph** in parts of *equal*
  size such that two vertices are adjacent if and only if they are in different parts.

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

open Finset Fintype Function

universe u
namespace SimpleGraph
variable {α : Type u}

/-- `G` is `IsCompleteMultipartite` iff non-adjacency is transitive -/
def IsCompleteMultipartite (G : SimpleGraph α) : Prop := Transitive (¬ G.Adj · ·)

theorem bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite := by
  simp [IsCompleteMultipartite, Transitive]

variable {G : SimpleGraph α}
/-- The setoid given by non-adjacency -/
def IsCompleteMultipartite.setoid (h : G.IsCompleteMultipartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless, fun h' ↦ by rwa [adj_comm] at h', fun h1 h2 ↦ h h1 h2⟩⟩

lemma completeMultipartiteGraph.isCompleteMultipartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompleteMultipartite := by
  intro
  simp_all

/-- The graph isomorphism from a graph `G` that `IsCompleteMultipartite` to the corresponding
`completeMultipartiteGraph` (see also `isCompleteMultipartite_iff`) -/
def IsCompleteMultipartite.iso (h : G.IsCompleteMultipartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) ↦ {x // h.setoid.r c.out x}) where
  toFun := fun x ↦ ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ ↦  x.1
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
    intro _ _ _ h1 h2
    rw [← e.map_rel_iff] at *
    exact completeMultipartiteGraph.isCompleteMultipartite _ h1 h2

lemma IsCompleteMultipartite.colorable_of_cliqueFree {n : ℕ} (h : G.IsCompleteMultipartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) :=
  (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ ↦ ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.toEmbedding).of_hom h.iso

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

@[grind]
lemma ne_fst (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₁ :=
  fun h ↦ h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind]
lemma ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₂ :=
  fun h ↦ h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind]
lemma fst_ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : w₁ ≠ w₂ := h2.adj.ne

@[symm] lemma symm (h : G.IsPathGraph3Compl v w₁ w₂) : G.IsPathGraph3Compl v w₂ w₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

end IsPathGraph3Compl

lemma exists_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite G) :
    ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ := by
  rw [IsCompleteMultipartite, Transitive] at h
  push_neg at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩

lemma not_isCompleteMultipartite_iff_exists_isPathGraph3Compl :
    ¬ IsCompleteMultipartite G ↔ ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ :=
  ⟨fun h ↦ G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ ↦ fun h ↦ h (by rwa [adj_comm] at h2) h3 h1⟩

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
  exact h h0 h1 h2

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

/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are a
*dependent* product type. -/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (const (Fin r) (Fin t)) :=
  { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

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
  rw [← not_iff_not, not_or, ← ne_eq, ← edgeSet_nonempty, not_le, ← Nat.succ_le_iff,
    ← Fin.nontrivial_iff_two_le, ← ne_eq, ← Nat.pos_iff_ne_zero, Fin.pos_iff_nonempty]
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

section IsCompleteMultipartiteBetween

variable {ι : Type*} {parts : ι → Set V}

def IsCompleteMultipartiteBetween (G : SimpleGraph V) (parts : ι → Set V) :=
  Pairwise fun ⦃i₁ i₂⦄ ↦
    ∀ ⦃v₁⦄, v₁ ∈ parts i₁ → ∀ ⦃v₂⦄, v₂ ∈ parts i₂ → G.Adj v₁ v₂

theorem IsCompleteMultipartiteBetween.pairwise_disjoint
    (h : G.IsCompleteMultipartiteBetween parts) : Pairwise (Disjoint on parts) :=
  fun _ _ hne ↦ Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (h hne hv₁ hv₂)

end IsCompleteMultipartiteBetween
of vertices each of size `t` such that vertices in distinct subsets are adjacent. -/
structure CompleteEquipartiteSubgraph (G : SimpleGraph V) (r t : ℕ) where
  /-- The `r` parts. -/
  parts : Fin r → Finset V
  /-- Each part is size `t`. -/
  card_parts (i : Fin r) : #(parts i) = t
  /-- Vertices in distinct parts are adjacent. -/
  Adj : Pairwise (fun ⦃i₁ i₂⦄ ↦ ∀ ⦃v₁⦄, v₁ ∈ parts i₁ → ∀ ⦃v₂⦄, v₂ ∈ parts i₂ → G.Adj v₁ v₂)

variable {r t : ℕ} (A : G.CompleteEquipartiteSubgraph r t)

namespace CompleteEquipartiteSubgraph

/-- The parts in a `G.CompleteEquipartiteSubgraph r t` are pairwise disjoint. -/
theorem pairwise_disjoint_on_parts : Pairwise (Disjoint on A.parts) :=
  fun _ _ hne ↦ disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (A.Adj hne hv₁ hv₂)

/-- The finset of vertices in a `G.CompleteEquipartiteSubgraph r t`. -/
abbrev verts : Finset V :=
  univ.disjiUnion A.parts (A.pairwise_disjoint_on_parts.set_pairwise univ.toSet)

/-- There are `r * t` vertices in a complete equipartite subgraph with `r` parts of size `t`. -/
theorem card_verts : #A.verts = r * t := by simp [card_parts]

/-- A complete equipartite subgraph gives rise to a copy of a complete equipartite graph. -/
noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  have (i : Fin r) : Nonempty (Fin t ↪ A.parts i) := by
    rw [Embedding.nonempty_iff_card_le, Fintype.card_fin, card_coe, A.card_parts i]
  have fᵣ (i : Fin r) : Fin t ↪ A.parts i := Classical.arbitrary (Fin t ↪ A.parts i)
  let f : (Fin r) × (Fin t) ↪ V := by
    use fun (i, x) ↦ fᵣ i x
    intro (i₁, x₁) (i₂, x₂) heq
    rw [Prod.mk.injEq]
    contrapose! heq with hne
    rcases eq_or_ne i₁ i₂ with heq | hne
    · rw [heq, ← Subtype.ext_iff.ne]
      exact (fᵣ i₂).injective.ne (hne heq)
    · exact (A.Adj hne (fᵣ i₁ x₁).prop (fᵣ i₂ x₂).prop).ne
  use ⟨f, ?_⟩, f.injective
  intro (i₁, x₁) (i₂, x₂) hne
  exact A.Adj hne (fᵣ i₁ x₁).prop (fᵣ i₂ x₂).prop

/-- A copy of a complete equipartite graph identifies a complete equipartite subgraph. -/
def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartiteSubgraph r t where
  parts i := by
    let fᵣ (i : Fin r) : Fin t ↪ V := by
      use fun x ↦ f (i, x)
      intro _ _ h
      simpa using f.injective h
    exact univ.map (fᵣ i)
  card_parts i := by simp
  Adj _ _ hne _ h₁ _ h₂ := by
    rw [mem_map] at h₁ h₂
    obtain ⟨_, _, h₁⟩ := h₁
    obtain ⟨_, _, h₂⟩ := h₂
    rw [← h₁, ← h₂]
    exact f.toHom.map_adj hne

end CompleteEquipartiteSubgraph

/-- Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type
`G.CompleteEquipartiteSubgraph r t` is nonempty. -/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ ↦ ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨A⟩ ↦ ⟨A.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (n + 1) t` iff there exists
`s : Finset V` of size `#s = t` and `A : G.CompleteEquipartiteSubgraph n t` such that the vertices
in `s` are adjacent to the vertices in `A`. -/
theorem completeEquipartiteGraph_succ_isContained_iff {n : ℕ} :
  completeEquipartiteGraph (n + 1) t ⊑ G
    ↔ ∃ᵉ (A : G.CompleteEquipartiteSubgraph n t) (s : Finset V),
      #s = t ∧ ∀ v₁ ∈ s, ∀ i, ∀ v₂ ∈ A.parts i, G.Adj v₁ v₂ := by
  rw [completeEquipartiteGraph_isContained_iff]
  refine ⟨fun ⟨A'⟩ ↦ ?_, fun ⟨A, s, hs, hadj⟩ ↦ ?_⟩
  · let A : G.CompleteEquipartiteSubgraph n t := by
      refine ⟨fun i ↦ A'.parts i.castSucc, fun i ↦ A'.card_parts i.castSucc, ?_⟩
      intro i₁ i₂ hne v₁ hv₁ v₂ hv₂
      rw [← Fin.castSucc_inj.ne] at hne
      exact A'.Adj hne hv₁ hv₂
    refine ⟨A, A'.parts (Fin.last n), A'.card_parts (Fin.last n), fun v₁ hv₁ i v₂ hv₂ ↦ ?_⟩
    have hne : i.castSucc ≠ Fin.last n := Fin.exists_castSucc_eq.mp ⟨i, rfl⟩
    exact (A'.Adj hne hv₂ hv₁).symm
  · refine ⟨fun i ↦ if hi : ↑i < n then A.parts ⟨i, hi⟩ else s, fun i ↦ ?_,
      fun i₁ i₂ hne v₁ hv₁ v₂ hv₂ ↦ ?_⟩
    · by_cases hi : ↑i < n
      · simp [hi, A.card_parts ⟨i, hi⟩]
      · simp [hi, hs]
    · by_cases hi₁ : ↑i₁ < n <;> by_cases hi₂ : ↑i₂ < n
        <;> simp [hi₁, hi₂] at hne hv₁ hv₂ ⊢
      · have hne : i₁.castLT hi₁ ≠ i₂.castLT hi₂ := by
          simp [Fin.ext_iff, Fin.val_ne_of_ne hne]
        exact A.Adj hne hv₁ hv₂
      · exact (hadj v₂ hv₂ ⟨i₁, hi₁⟩ v₁ hv₁).symm
      · exact hadj v₁ hv₁ ⟨i₂, hi₂⟩ v₂ hv₂
      · absurd hne
        rw [Fin.ext_iff, Nat.eq_of_le_of_lt_succ (le_of_not_gt hi₁) i₁.isLt,
          Nat.eq_of_le_of_lt_succ (le_of_not_gt hi₂) i₂.isLt]

end CompleteEquipartiteSubgraph

end SimpleGraph
