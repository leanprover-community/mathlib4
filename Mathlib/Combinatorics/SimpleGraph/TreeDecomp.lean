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
public import Mathlib.Tactic.ENatToNat

/-!
# Tree Decompositions and Tree Width

This file defines tree decompositions on simple graphs and the treewidth.

## Main definitions

* `SimpleGraph.TreeDecomp` is a tree decomposition of a simple graph.
* `TreeDecomp.ewidth` is the extended width of the tree decomposition. `TreeDecomp.width` is the
  ℕ-valued version, and is equivalent to `ewidth` when there is `[Finite V]`.
* `SimpleGraph.HasTreeDecomp n` is a predicate that a simple graph has a tree decomposition of width
  at most n.
* `SimpleGraph.etreeWidth` is the extended tree width of a simple graph. `SimpleGraph.treeWidth` is
  the ℕ-valued version.

## Main statements

* `treeWidth_le_card` shows that a finite graph must have finite treewidth.

## References

* [R. Diestel **Graph Theory**
  https://doi.org/10.1007/978-3-662-70107-2][diestel2025]

## Tags

tree decomposition, treewidth

-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

universe u v
variable {V : Type u} {V' : Type v}
variable {G : SimpleGraph V} {G' : SimpleGraph V'}

/-- A tree decomposition of a simple graph `G` is a tree `T` indexed by a type
`W`, together with a bag `𝓧 w : Finset V` assigned to each `w : W`, such that
every edge of `G` lies in some bag and the bags containing any fixed vertex form
a connected subgraph of `T`. -/
structure TreeDecomp (G : SimpleGraph V) where
  /-- The type of bags in the tree. -/
  W : Type
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
  preconnected_induce_T : ∀ v : V, (T.induce ({w | v ∈ 𝓧 w})).Preconnected

instance (t : G.TreeDecomp) : Nonempty t.W := t.isTree.connected.nonempty

namespace TreeDecomp

/-- The width of a tree decomposition, as an extended natural number:
the maximum bag size minus one. -/
noncomputable def ewidth (t : G.TreeDecomp) : ℕ∞ :=
  ⨆ w : t.W, #(t.𝓧 w) - 1

/-- `ℕ`-valued view of `TreeDecomp.ewidth`. -/
noncomputable def width (t : G.TreeDecomp) : ℕ := t.ewidth.toNat

lemma ewidth_eq (t : G.TreeDecomp) :
    t.ewidth = ⨆ w : t.W, (#(t.𝓧 w) - 1 : ℕ∞) := rfl

lemma le_ewidth {k : ℕ} (t : G.TreeDecomp) :
    (∃ w : t.W, (k : ℕ∞) ≤ #(t.𝓧 w) - 1) → (k : ℕ∞) ≤ t.ewidth :=
  fun ⟨w, hw⟩ ↦ le_iSup_of_le w (by exact_mod_cast hw)

lemma ewidth_le_iff {k : ℕ} (t : G.TreeDecomp) :
    t.ewidth ≤ k ↔ ∀ w : t.W, #(t.𝓧 w) - 1 ≤ k := by
  rw [ewidth_eq, iSup_le_iff]
  enat_to_nat

/-- The cardinality of every bag is less than the ewidth + 1. -/
lemma card_bag_le_ewidth (t : G.TreeDecomp) (w : t.W) :
    #(t.𝓧 w) ≤ t.ewidth + 1 := by
  have : (#(t.𝓧 w) - 1 : ℕ∞) ≤ t.ewidth := le_iSup (fun w ↦ (#(t.𝓧 w) - 1 : ℕ∞)) w
  calc (#(t.𝓧 w) : ℕ∞) ≤ #(t.𝓧 w) - 1 + 1 := le_tsub_add
    _ ≤ t.ewidth + 1 := by gcongr

/-- G has a tree decomposition with width at most n. -/
def _root_.SimpleGraph.HasTreeDecomp (G : SimpleGraph V) (n : ℕ∞) : Prop :=
  ∃ t : G.TreeDecomp, t.ewidth ≤ n

@[mono]
lemma _root_.SimpleGraph.HasTreeDecomp.mono {n m : ℕ∞} (h : n ≤ m) :
    G.HasTreeDecomp n → G.HasTreeDecomp m :=
  fun ⟨t, ht⟩ ↦ ⟨t, ht.trans h⟩

@[simp]
lemma coe_width {t : G.TreeDecomp} (h : t.ewidth ≠ ⊤) :
    (t.width : ℕ∞) = t.ewidth := ENat.coe_toNat h

/-- Every bag in a tree decomposition has size at most width + 1. -/
lemma card_bag_le_width (t : G.TreeDecomp) (hwidth : t.ewidth ≠ ⊤) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := by
  have := t.card_bag_le_ewidth w
  rw [← t.coe_width hwidth] at this
  exact_mod_cast this

/-- A tree decomposition has width at least k iff some bag has bag size at least k + 1. -/
lemma le_width_iff {k : ℕ} (t : G.TreeDecomp) (hwidth : t.ewidth ≠ ⊤) :
    k ≤ t.width ↔ ∃ w : t.W, k ≤ #(t.𝓧 w) - 1 := by
  suffices (k : ℕ∞) ≤ t.ewidth ↔ (∃ w : t.W, (k : ℕ∞) ≤ #(t.𝓧 w) - 1) by
    rw [← t.coe_width hwidth] at this; exact_mod_cast this
  refine ⟨fun h ↦ ?_, t.le_ewidth⟩
  obtain ⟨w, hw⟩ := ENat.exists_eq_iSup_of_lt_top hwidth.lt_top
  exact ⟨w, hw.symm ▸ h⟩

/-- A tree decomposition has width ≤ k iff every bag has bag size - 1 ≤ k. -/
lemma width_le_iff {k : ℕ} (t : G.TreeDecomp) (hwidth : t.ewidth ≠ ⊤) :
    t.width ≤ k ↔ ∀ w : t.W, #(t.𝓧 w) - 1 ≤ k := by
  rw [← Nat.cast_le (α := ℕ∞), t.coe_width hwidth, t.ewidth_le_iff]

/-- On a finite vertex type, every tree decomposition has `width` at most `card V - 1`. -/
lemma ewidth_le_card_sub_one [Fintype V] (t : G.TreeDecomp) :
    t.ewidth ≤ card V - 1 :=
  iSup_le fun _ ↦ by
    exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_univ _) 1

/-- On a finite vertex type, every tree decomposition has finite extended width. -/
lemma ewidth_ne_top_of_finite [Finite V] (t : G.TreeDecomp) : t.ewidth ≠ ⊤ := by
  have := Fintype.ofFinite V
  exact (t.ewidth_le_card_sub_one.trans_lt (ENat.coe_lt_top _)).ne

@[simp]
lemma coe_width_of_finite [Finite V] (t : G.TreeDecomp) :
    (t.width : ℕ∞) = t.ewidth := t.coe_width t.ewidth_ne_top_of_finite

lemma width_le_iff_ewidth_le [Finite V] (t : G.TreeDecomp) {k : ℕ} :
    t.width ≤ k ↔ t.ewidth ≤ k := by
  rw [← t.coe_width_of_finite]; enat_to_nat

/-- On a finite vertex type, every tree decomposition has width at most `card V - 1`. -/
lemma width_le_card_sub_one [Fintype V] (t : G.TreeDecomp) :
    t.width ≤ card V - 1 := by
  exact_mod_cast t.coe_width_of_finite ▸ t.ewidth_le_card_sub_one

/-- Each bag of a tree decomposition has cardinality at most `width + 1` (finite-vertex form). -/
lemma card_bag_le_width_of_finite [Finite V] (t : G.TreeDecomp) (w : t.W) :
    #(t.𝓧 w) ≤ t.width + 1 := t.card_bag_le_width t.ewidth_ne_top_of_finite w

/-- Transport a tree decomposition along a graph isomorphism by mapping each bag. -/
noncomputable def iso (φ : G ≃g G') (t : G.TreeDecomp) : G'.TreeDecomp := { t with
  𝓧 w := (t.𝓧 w).map φ
  vertexCover v' := (t.vertexCover (φ.symm v')).imp fun _ ↦ Finset.mem_map_equiv.mpr
  edgeCover u' v' huv :=
    (t.edgeCover (φ.symm.map_rel_iff.mpr huv)).imp fun _ ⟨hu, hv⟩ ↦
      ⟨Finset.mem_map_equiv.mpr hu, Finset.mem_map_equiv.mpr hv⟩
  preconnected_induce_T v' := by
    have : {w : t.W | v' ∈ (t.𝓧 w).map φ} = {w | φ.symm v' ∈ t.𝓧 w} := by
      ext; exact Finset.mem_map_equiv
    exact this ▸ t.preconnected_induce_T (φ.symm v') }

@[simp]
lemma ewidth_iso (φ : G ≃g G') (t : G.TreeDecomp) :
    (t.iso φ).ewidth = t.ewidth := by
  simp only [ewidth_eq, iso, Finset.card_map]

lemma _root_.SimpleGraph.Iso.hasTreeDecomp_iff {n : ℕ∞} (φ : G ≃g G') :
    G.HasTreeDecomp n ↔ G'.HasTreeDecomp n :=
  ⟨fun ⟨t, ht⟩ ↦ ⟨t.iso φ, ewidth_iso φ t ▸ ht⟩,
   fun ⟨t, ht⟩ ↦ ⟨t.iso φ.symm, ewidth_iso φ.symm t ▸ ht⟩⟩

/-- Pull back a tree decomposition along a graph embedding by taking the preimage of each bag. -/
noncomputable def comap (f : G ↪g G') (t : G'.TreeDecomp) : G.TreeDecomp where
  W := t.W
  𝓧 w := (t.𝓧 w).preimage f f.injective.injOn
  T := t.T
  isTree := t.isTree
  vertexCover v := (t.vertexCover (f v)).imp fun _ ↦ Finset.mem_preimage.mpr
  edgeCover u v huv :=
    (t.edgeCover (f.map_rel_iff.mpr huv)).imp fun _ ⟨hu, hv⟩ ↦
      ⟨Finset.mem_preimage.mpr hu, Finset.mem_preimage.mpr hv⟩
  preconnected_induce_T v := by
    have : {w : t.W | v ∈ (t.𝓧 w).preimage f f.injective.injOn} = {w | f v ∈ t.𝓧 w} := by
      ext; exact Finset.mem_preimage
    exact this ▸ t.preconnected_induce_T (f v)

lemma ewidth_comap_le (f : G ↪g G') (t : G'.TreeDecomp) :
    (t.comap f).ewidth ≤ t.ewidth := by
  refine iSup_mono fun w ↦ ?_
  gcongr
  change ((t.𝓧 w).preimage f f.injective.injOn).card ≤ (t.𝓧 w).card
  exact Finset.card_le_card_of_injOn f
    (fun v hv ↦ Finset.mem_preimage.mp hv) f.injective.injOn

lemma _root_.SimpleGraph.hasTreeDecomp_of_embedding {n : ℕ∞} (f : G ↪g G') :
    G'.HasTreeDecomp n → G.HasTreeDecomp n :=
  fun ⟨t, ht⟩ ↦ ⟨t.comap f, (ewidth_comap_le f t).trans ht⟩

/-- The tree decomposition of `⊥`, represented as a star graph with `none` as the center, and an
element of `V` at each leaf. The vertex set `V` is encoded as `Fin (Fintype.card V) : Type 0` for
W to fit in `Type 0`. -/
protected noncomputable def bot [Fintype V] : (⊥ : SimpleGraph V).TreeDecomp where
  W := Option (Fin (Fintype.card V))
  𝓧 w := w.elim ∅ (fun i ↦ {(Fintype.equivFin V).symm i})
  T := starGraph none
  isTree := isTree_starGraph _
  vertexCover v := ⟨some (Fintype.equivFin V v), by simp⟩
  edgeCover _ _ h := h.elim
  preconnected_induce_T v := by
    have : {w : Option (Fin (Fintype.card V)) |
        v ∈ w.elim ∅ (fun i ↦ ({(Fintype.equivFin V).symm i} : Finset V))} =
        {some (Fintype.equivFin V v)} := by
      ext (_ | i) <;> simp [Equiv.eq_symm_apply, eq_comm]
    exact this ▸ Preconnected.of_subsingleton

lemma _root_.SimpleGraph.ewidth_botTreeDecomp [Fintype V] :
    (TreeDecomp.bot (V := V)).ewidth = 0 := by
  refine iSup_eq_bot.mpr ?_
  rintro (_ | w) <;> simp [TreeDecomp.bot]

/-- If G has a tree decomposition of width n, then the same decomposition applies for any
  subgraph. -/
@[gcongr]
lemma _root_.SimpleGraph.hasTreeDecomp_mono {G' : SimpleGraph V} {n : ℕ∞} (h : G' ≤ G)
    (hG : G.HasTreeDecomp n) : G'.HasTreeDecomp n := by
  obtain ⟨t, ht⟩ := hG
  exact ⟨{ t with edgeCover _ _ huv := t.edgeCover (h huv)}, ht⟩

end TreeDecomp

section TreeWidth

/-- The (extended) tree width of a simple graph is the infimum of widths over all tree
decompositions. -/
noncomputable def etreeWidth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ t : G.TreeDecomp, t.ewidth

/-- `ℕ`-valued view of `etreeWidth`, with junk value `0` when the treewidth is `⊤`. -/
noncomputable def treeWidth (G : SimpleGraph V) : ℕ := G.etreeWidth.toNat

lemma etreeWidth_le_ewidth (t : G.TreeDecomp) : G.etreeWidth ≤ t.ewidth :=
  iInf_le _ t

@[simp]
lemma coe_treeWidth (h : G.etreeWidth ≠ ⊤) : G.treeWidth = G.etreeWidth := ENat.coe_toNat h

/-- G has extended treewidth at most k iff G has a tree decomposition of width k, where k is finite.
-/
lemma etreeWidth_le_iff_hasTreeDecomp (k : ℕ) :
    G.etreeWidth ≤ k ↔ G.HasTreeDecomp k := by
  refine ⟨fun h ↦ ?_, fun h ↦ (etreeWidth_le_ewidth h.choose).trans h.choose_spec⟩
  by_contra hc
  rw [HasTreeDecomp, not_exists] at hc
  have : (k + 1 : ℕ∞) ≤ G.etreeWidth :=
    le_iInf fun t ↦ (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr (not_le.mp (hc t))
  exact absurd (this.trans h) (by enat_to_nat; omega)

lemma le_etreeWidth_iff {k : ℕ∞} : k ≤ G.etreeWidth ↔ ∀ t : G.TreeDecomp, k ≤ t.ewidth :=
  le_iInf_iff

/-- The tree decomposition obtained by putting all vertices in one bag. -/
protected def trivialTreeDecomp [Fintype V] (G : SimpleGraph V) : G.TreeDecomp where
  W := Unit
  𝓧 _ := univ
  T := ⊥
  isTree := IsTree.of_subsingleton
  vertexCover := by simp
  edgeCover := by simp
  preconnected_induce_T := by aesop_graph

lemma ewidth_trivialTreeDecomp [Fintype V] :
    (G.trivialTreeDecomp).ewidth = (card V - 1 : ℕ) := by
  simp [TreeDecomp.ewidth_eq, SimpleGraph.trivialTreeDecomp]

/-- The treewidth of a finite graph is at most `card V - 1`. -/
lemma etreeWidth_le_card [Fintype V] : G.etreeWidth ≤ card V - 1 :=
  (etreeWidth_le_ewidth G.trivialTreeDecomp).trans ewidth_trivialTreeDecomp.le

@[gcongr]
lemma etreeWidth_mono {G' : SimpleGraph V} (h : G' ≤ G) : G'.etreeWidth ≤ G.etreeWidth := by
  cases hw : G.etreeWidth
  · simp
  · expose_names
    rw [etreeWidth_le_iff_hasTreeDecomp]
    exact G.hasTreeDecomp_mono h ((etreeWidth_le_iff_hasTreeDecomp a).mp hw.le)

lemma etreeWidth_mono_of_embedding (f : G ↪g G') : G.etreeWidth ≤ G'.etreeWidth := by
  cases hw : G'.etreeWidth
  · simp
  · expose_names
    rw [etreeWidth_le_iff_hasTreeDecomp]
    exact hasTreeDecomp_of_embedding f ((etreeWidth_le_iff_hasTreeDecomp a).mp hw.le)

/-- On a finite vertex type, the extended treewidth is finite. -/
lemma etreeWidth_ne_top_of_finite [Finite V] : G.etreeWidth ≠ ⊤ := by
  have := Fintype.ofFinite V
  exact (etreeWidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

@[simp]
lemma coe_treeWidth_of_finite [Finite V] : (G.treeWidth : ℕ∞) = G.etreeWidth :=
  coe_treeWidth etreeWidth_ne_top_of_finite

@[simp]
lemma treeWidth_le_iff_etreeWidth_le [Finite V] {k : ℕ} :
    G.treeWidth ≤ k ↔ G.etreeWidth ≤ k := by
  rw [← coe_treeWidth_of_finite]; enat_to_nat

/-- G has treewidth at most `k` (as a natural number) iff it has a tree decomposition of width
at most `k`. -/
theorem treeWidth_le_iff_hasTreeDecomp [Finite V] (k : ℕ) :
    G.treeWidth ≤ k ↔ G.HasTreeDecomp k :=
  treeWidth_le_iff_etreeWidth_le.trans (etreeWidth_le_iff_hasTreeDecomp k)

lemma le_treeWidth_iff [Finite V] {k : ℕ} :
    k ≤ G.treeWidth ↔ ∀ t : G.TreeDecomp, k ≤ t.width := by
  simp [← Nat.cast_le (α := ℕ∞), le_etreeWidth_iff]

/-- The treewidth of a finite graph is at most `card V - 1`. -/
theorem treeWidth_le_card [Fintype V] : G.treeWidth ≤ card V - 1 :=
  treeWidth_le_iff_etreeWidth_le.mpr etreeWidth_le_card

@[gcongr]
lemma treeWidth_mono {G' : SimpleGraph V} [Finite V] (h : G' ≤ G) : G'.treeWidth ≤ G.treeWidth := by
  simpa using etreeWidth_mono h

lemma treeWidth_mono_of_embedding [Finite V] [Finite V']
    (f : G ↪g G') : G.treeWidth ≤ G'.treeWidth := by
  simpa using etreeWidth_mono_of_embedding f

/-- Extended treewidth is monotone under graph containment. -/
theorem IsContained.etreeWidth_le {A : SimpleGraph V} {B : SimpleGraph V'} (h : A ⊑ B) :
    A.etreeWidth ≤ B.etreeWidth := by
  obtain ⟨f⟩ := h
  calc A.etreeWidth
      ≤ f.toSubgraph.coe.etreeWidth :=
        etreeWidth_mono_of_embedding f.isoToSubgraph.toEmbedding
    _ ≤ f.toSubgraph.spanningCoe.etreeWidth :=
        etreeWidth_mono_of_embedding f.toSubgraph.coeEmbeddingSpanningCoe
    _ ≤ B.etreeWidth := etreeWidth_mono f.toSubgraph.spanningCoe_le

theorem IsContained.treeWidth_le {A : SimpleGraph V} {B : SimpleGraph V'}
    [Finite V] [Finite V'] (h : A ⊑ B) : A.treeWidth ≤ B.treeWidth := by
  simpa using h.etreeWidth_le

/-- The treewidth of the empty graph is 0. -/
lemma treeWidth_bot [Finite V] : (⊥ : SimpleGraph V).treeWidth = 0 := by
  have := Fintype.ofFinite V
  have : (⊥ : SimpleGraph V).etreeWidth = 0 :=
    le_antisymm ((etreeWidth_le_ewidth TreeDecomp.bot).trans ewidth_botTreeDecomp.le) zero_le
  simp [treeWidth, this]

/-- The treewidth of a graph is positive iff it has an edge. -/
@[simp]
theorem treeWidth_pos [Finite V] : 0 < G.treeWidth ↔ G ≠ ⊥ := by
  classical
  have := Fintype.ofFinite V
  constructor
  · contrapose!
    intro h
    exact (h ▸ treeWidth_bot).le
  · rw [← Order.one_le_iff_pos, le_treeWidth_iff, SimpleGraph.ne_bot_iff_exists_adj]
    rintro ⟨u, v, huv⟩ t
    obtain ⟨w, hu, hv⟩ := t.edgeCover huv
    have := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv.ne⟩
    exact (t.le_width_iff t.ewidth_ne_top_of_finite).mpr ⟨w, by omega⟩

@[simp]
lemma treeWidth_eq_zero [Finite V] : G.treeWidth = 0 ↔ G = ⊥ := by
  rw [← not_iff_not, ← ne_eq, ← Nat.pos_iff_ne_zero]
  exact treeWidth_pos

lemma treeWidth_ne_zero [Finite V] : G.treeWidth ≠ 0 ↔ G ≠ ⊥ := by
  simp only [ne_eq, treeWidth_eq_zero]

end TreeWidth
end SimpleGraph
