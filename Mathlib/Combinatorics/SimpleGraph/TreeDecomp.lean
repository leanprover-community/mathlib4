/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Int.Cast.Basic

/-!
# Tree Decompositions and Tree Width

This file defines tree decompositions on simple graphs and the treewidth parameter.

## Main definitions

* `SimpleGraph.TreeDecomp` is a tree decomposition of a simple graph.
* `TreeDecomp.ewidth` is the extended width of the tree decomposition. `SimpleGraph.width` is the
  ℕ-valued version.
* `SimpleGraph.hasTreeDecomp n` is a predicate that a simple graph has a tree decomposition of width
  at most n.
* `SimpleGraph.etreeWidth` is the extended tree width of a simple graph. `SimpleGraph.treewidth` is
  the ℕ-valued version.

## Main statements

* `treeWidth_le_card` shows that a finite graph must have finite treewidth.
* `etreeWidth_ne_zero_iff_ne_bot` shows that a graph has nonzero treewidth iff it is nonempty.

## References

* [R. Diestel **Graph Theory**
  https://doi.org/10.1007/978-3-662-70107-2][diestel2025]

## TODO

* Prove `G.IsAcyclic ↔ G.treewidth ≤ 1`.
* Prove that a complete graph with `n` vertices has treewidth `n`.

## Tags
tree decomposition, treewidth

-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

universe u v
variable {V V' : Type u}
variable {G : SimpleGraph V} {G' : SimpleGraph V'}

/-! ## Tree decompositions -/

section TreeDecomp

/-- A tree decomposition of a simple graph `G` is a tree `T` indexed by a type
`W`, together with a bag `𝓧 w : Finset V` assigned to each `w : W`, such that
every edge of `G` lies in some bag and the bags containing any fixed vertex form
a connected subgraph of `T`. -/
structure TreeDecomp (G : SimpleGraph V) where
  /-- The type of bags in the tree. -/
  W : Type u
  /-- The set of vertices in each bag. -/
  𝓧 : W → Finset V
  /-- The graph adjacency relation of bags. -/
  T : SimpleGraph W
  /-- T must be a tree. -/
  isTree : IsTree T
  /-- All vertices in G must appear in some bag. -/
  vertexCover : ∀ v : V, ∃ w : W, v ∈ 𝓧 w
  /-- For any edge (u, v) in G, there is a bag containing both u and v. -/
  edgeCover ⦃u v : V⦄ : G.Adj u v → ∃ w : W, u ∈ 𝓧 w ∧ v ∈ 𝓧 w
  /-- For any vertex v in G, the set of bags that contain v is preconnected. -/
  connectedBags : ∀ v : V, (T.induce ({w | v ∈ 𝓧 w})).Preconnected

/-- The width of a tree decomposition, as an extended natural number:
the maximum bag size minus one. -/
noncomputable def TreeDecomp.ewidth (t : TreeDecomp G) : ℕ∞ :=
  ⨆ w : t.W, #(t.𝓧 w) - 1

/-- `ℕ`-valued view of `TreeDecomp.ewidth`, with junk value `0` when the width is `⊤`. -/
noncomputable def TreeDecomp.width (t : TreeDecomp G) : ℕ := t.ewidth.toNat

lemma TreeDecomp.ewidth_eq (t : TreeDecomp G) :
    t.ewidth = ⨆ w : t.W, (#(t.𝓧 w) - 1 : ℕ∞) := rfl

lemma TreeDecomp.ewidth_ge {k : ℕ} (t : TreeDecomp G) :
    (∃ w : t.W, #(t.𝓧 w) - 1 ≥ k) → t.ewidth ≥ k :=
  fun ⟨w, hw⟩ ↦ le_iSup_of_le w (by exact_mod_cast hw)

/-- G has a tree decomposition with width at most n. -/
def hasTreeDecomp (G : SimpleGraph V) (n : ℕ∞) : Prop := ∃ t : G.TreeDecomp, t.ewidth ≤ n

@[mono]
lemma hasTreeDecomp.mono {n m : ℕ∞} (h : n ≤ m) : G.hasTreeDecomp n → G.hasTreeDecomp m := by
  intro ⟨t, ht⟩
  use t
  exact le_trans ht h

/-- Transport a tree decomposition along a graph isomorphism by mapping each bag. -/
noncomputable def TreeDecomp.map (φ : G ≃g G') (t : G.TreeDecomp) : G'.TreeDecomp := { t with
  𝓧 w := (t.𝓧 w).map φ
  vertexCover v' := (t.vertexCover (φ.symm v')).imp fun _ ↦ Finset.mem_map_equiv.mpr
  edgeCover u' v' huv :=
    (t.edgeCover (φ.symm.map_rel_iff.mpr huv)).imp fun _ ⟨hu, hv⟩ ↦
      ⟨Finset.mem_map_equiv.mpr hu, Finset.mem_map_equiv.mpr hv⟩
  connectedBags v' := by
    have : {w : t.W | v' ∈ (t.𝓧 w).map φ} = {w | φ.symm v' ∈ t.𝓧 w} := by
      ext; exact Finset.mem_map_equiv
    exact this ▸ t.connectedBags (φ.symm v') }

@[simp]
lemma TreeDecomp.ewidth_map (φ : G ≃g G') (t : G.TreeDecomp) : (t.map φ).ewidth = t.ewidth := by
  simp only [TreeDecomp.ewidth_eq, TreeDecomp.map, Finset.card_map]

lemma Iso.hasTreeDecomp_iff {n : ℕ∞} {V' : Type u}
    {G : SimpleGraph V} {G' : SimpleGraph V'} (φ : G ≃g G') :
    G.hasTreeDecomp n ↔ G'.hasTreeDecomp n :=
  ⟨fun ⟨t, ht⟩ ↦ ⟨t.map φ, TreeDecomp.ewidth_map φ t ▸ ht⟩,
   fun ⟨t, ht⟩ ↦ ⟨t.map φ.symm, TreeDecomp.ewidth_map φ.symm t ▸ ht⟩⟩

@[simp]
lemma TreeDecomp.coe_width (t : TreeDecomp G) (h : t.ewidth ≠ ⊤) :
    (t.width : ℕ∞) = t.ewidth := ENat.coe_toNat h

/-- The tree decomposition obtained by putting all vertices in one bag. -/
def trivialTreeDecomp [Fintype V] (G : SimpleGraph V) : G.TreeDecomp where
  W := ULift.{u} Unit
  𝓧 := fun _ ↦ univ
  T := ⊥
  isTree := by exact IsTree.of_subsingleton
  vertexCover := by simp
  edgeCover := by simp
  connectedBags := by aesop_graph

lemma ewidth_trivialTreeDecomp [Fintype V] :
    (G.trivialTreeDecomp).ewidth = (card V - 1 : ℕ) := by
  simp [TreeDecomp.ewidth_eq, trivialTreeDecomp]

/-- The tree decomposition of `⊥` indexed by `Option V` with a star graph rooted at `none`:
bags are `∅` at `none` and `{v}` at `some v`. -/
noncomputable def botTreeDecomp : (⊥ : SimpleGraph V).TreeDecomp where
  W := Option V
  𝓧 w := w.elim ∅ ({·})
  T := starGraph none
  isTree := isTree_starGraph _
  vertexCover v := ⟨some v, by simp⟩
  edgeCover _ _ h := h.elim
  connectedBags v := by
    have : {w : Option V | v ∈ w.elim ∅ ({·} : V → Finset V)} = {some v} := by
      ext w
      cases w <;> simp [eq_comm]
    exact this ▸ Preconnected.of_subsingleton

lemma ewidth_botTreeDecomp : (botTreeDecomp (V := V)).ewidth = 0 := by
  refine iSup_eq_bot.mpr ?_
  rintro (_ | w) <;> simp [botTreeDecomp]


/-- If G has a tree decomposition of width n, then the same decomposition on any subgraph. -/
@[mono]
lemma TreeDecomp.mono {G' : SimpleGraph V} {n : ℕ∞} (h : G' ≤ G) (hG : G.hasTreeDecomp n) :
    G'.hasTreeDecomp n := by
  obtain ⟨t, ht⟩ := hG
  exact ⟨{ t with edgeCover := fun _ _ huv ↦ t.edgeCover (h huv)}, ht⟩

/-- On a finite vertex type, every tree decomposition has `width` at most `card V - 1`. -/
lemma TreeDecomp.ewidth_le_card [Fintype V] (t : TreeDecomp G) :
    t.ewidth ≤ card V - 1 :=
  iSup_le fun _ ↦ by
    exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_univ _) 1

@[simp]
lemma TreeDecomp.coe_width_of_finite [Finite V] (t : TreeDecomp G) :
    (t.width : ℕ∞) = t.ewidth := by
  have := Fintype.ofFinite V
  exact t.coe_width (t.ewidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

/-- On a finite vertex type, every tree decomposition has width at most `card V - 1`. -/
lemma TreeDecomp.width_le_card [Fintype V] (t : TreeDecomp G) :
    t.width ≤ card V - 1 := by
  exact_mod_cast t.coe_width_of_finite ▸ t.ewidth_le_card

end TreeDecomp

/-! ## Tree width -/

section TreeWidth

/-- The tree width of a simple graph, as an extended natural number:
the infimum of widths over all tree decompositions, valued in `ℕ∞`. -/
noncomputable def etreeWidth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ t : TreeDecomp G, t.ewidth

/-- `ℕ`-valued view of `etreeWidth`, with junk value `0` when the treewidth is `⊤`. -/
noncomputable def treeWidth (G : SimpleGraph V) : ℕ := G.etreeWidth.toNat

lemma treeDecomp_imp_etreeWidth_le (treeDecomp : G.TreeDecomp) :
    G.etreeWidth ≤ treeDecomp.ewidth :=
  iInf_le _ treeDecomp

@[simp]
lemma coe_treeWidth (h : G.etreeWidth ≠ ⊤) : G.treeWidth = G.etreeWidth := ENat.coe_toNat h

/-- G has extended treewidth ≤ k iff G has a tree decomposition of width k, where k is finite. -/
@[simp]
lemma etreeWidth_le_iff_hasTreeDecomp (k : ℕ) :
    G.etreeWidth ≤ k ↔ G.hasTreeDecomp k := by
  refine ⟨fun h ↦ ?_, fun h ↦ (treeDecomp_imp_etreeWidth_le h.choose).trans h.choose_spec⟩
  by_contra hc
  rw [hasTreeDecomp, not_exists] at hc
  have : (k + 1 : ℕ∞) ≤ G.etreeWidth := by
    exact le_iInf fun t ↦ (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr (not_le.mp (hc t))
  exact absurd (this.trans h) (by exact_mod_cast Nat.not_succ_le_self k)

/-- The treewidth of a finite graph is at most `card V - 1`. -/
lemma etreeWidth_le_card [Fintype V] : G.etreeWidth ≤ card V - 1 :=
  (treeDecomp_imp_etreeWidth_le G.trivialTreeDecomp).trans ewidth_trivialTreeDecomp.le

@[gcongr]
lemma etreeWidth_mono {G' : SimpleGraph V} (h : G' ≤ G) : G'.etreeWidth ≤ G.etreeWidth := by
  cases hw : G.etreeWidth
  · simp
  · expose_names
    rw [etreeWidth_le_iff_hasTreeDecomp]
    exact TreeDecomp.mono h ((etreeWidth_le_iff_hasTreeDecomp a).mp hw.le)

@[simp]
lemma coe_treeWidth_of_finite [Finite V] :
    (G.treeWidth : ℕ∞) = G.etreeWidth := by
  have := Fintype.ofFinite V
  exact coe_treeWidth (etreeWidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

/-- The treewidth of a finite graph is at most `card V - 1`. -/
theorem treeWidth_le_card [Fintype V] :
    G.treeWidth ≤ card V - 1 := by
  exact_mod_cast coe_treeWidth_of_finite (V := V) ▸ etreeWidth_le_card (G := G)

@[gcongr]
lemma treeWidth_mono {G' : SimpleGraph V} [Finite V] (h : G' ≤ G) : G'.treeWidth ≤ G.treeWidth := by
  suffices (G'.treeWidth : ℕ∞) ≤ G.treeWidth by exact_mod_cast this
  simpa using etreeWidth_mono h

/-- The treewidth of a graph is nonzero iff it has an edge. -/
theorem etreeWidth_ne_zero_iff_ne_bot : 0 < G.etreeWidth ↔ G ≠ ⊥ := by
  classical
  constructor
  · contrapose!
    rintro rfl
    exact (treeDecomp_imp_etreeWidth_le botTreeDecomp).trans ewidth_botTreeDecomp.le
  · rw [SimpleGraph.ne_bot_iff_exists_adj]
    rintro ⟨u, v, huv⟩
    by_contra! hle
    obtain ⟨t, ht⟩ := (etreeWidth_le_iff_hasTreeDecomp 0).mp hle
    obtain ⟨w, hu, hv⟩ := t.edgeCover huv
    have hw : (1 : ℕ∞) ≤ t.ewidth := by
      exact_mod_cast t.ewidth_ge ⟨w, by
        have := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv.ne⟩; omega⟩
    exact absurd (hw.trans ht) (by decide)

@[simp]
lemma etreeWidth_bot : (⊥ : SimpleGraph V).etreeWidth = 0 :=
  le_antisymm ((treeDecomp_imp_etreeWidth_le botTreeDecomp).trans ewidth_botTreeDecomp.le)
    (zero_le _)

@[simp]
lemma treeWidth_bot : (⊥ : SimpleGraph V).treeWidth = 0 := by
  simp [treeWidth]

end TreeWidth

section Adhesion

/-- Given a tree decomposition (𝓧, T), the adhesion set is the intersection of bags along some edge
  in T. -/
def TreeDecomp.adhesion [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (_ : t.T.Adj x y)
    : Finset V := (t.𝓧 x) ∩ (t.𝓧 y)

-- TODO: Restate using subtree notation.
/-- If v is not in an adhesion set, all bags containing v must reside in some subtree cut by the
    adhesion set's edge. -/
theorem adhesion_imp_separator [DecidableEq V] (t : G.TreeDecomp) {x y : t.W} (h : t.T.Adj x y) :
    ∀ v ∉ t.adhesion h, ∀ a b : t.W, v ∈ t.𝓧 a → v ∈ t.𝓧 b →
    ∀ p : t.T.Path a b, s(x, y) ∉ p.val.edges := by
  classical
  intro v hv a b ha hb p hxy
  apply hv
  simp only [TreeDecomp.adhesion, Finset.mem_inter]
  obtain ⟨q⟩ := t.connectedBags v ⟨a, ha⟩ ⟨b, hb⟩
  let q' : t.T.Walk a b := q.map (Embedding.induce _).toHom
  have hpath : q'.toPath = p := t.isTree.isAcyclic.path_unique _ _
  have hq_support : ∀ w ∈ q'.support, v ∈ t.𝓧 w := by
    change ∀ w ∈ (q.map (Embedding.induce _).toHom).support, v ∈ t.𝓧 w
    simp only [Walk.support_map, List.mem_map]
    rintro w ⟨⟨w', hw'⟩, _, rfl⟩
    exact hw'
  have hp_sub : p.val.support ⊆ q'.support := hpath ▸ Walk.support_toPath_subset q'
  exact ⟨hq_support x (hp_sub (p.val.fst_mem_support_of_mem_edges hxy)),
    hq_support y (hp_sub (p.val.snd_mem_support_of_mem_edges hxy))⟩

end Adhesion

end SimpleGraph
