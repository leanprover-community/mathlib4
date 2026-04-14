/-
Copyright (c) 2026 Jhao-Syun Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jhao-Syun Lai
-/
module

import Mathlib.Tactic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Int.Cast.Basic

/-!
# Tree Decompositions and Tree Width

This file defines tree decompositions on simple graphs and the tree width.
-/

open Finset Fintype

namespace SimpleGraph

universe u
variable {V : Type u}

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
  /-- For any edge (u, v) in G, there is a bag containing both u and v. -/
  edgeCover : ∀ u v : V, G.Adj u v → ∃ w : W, u ∈ 𝓧 w ∧ v ∈ 𝓧 w
  /-- For any vertex v in G, the set of bags that contain v is nonempty and connected. -/
  connectedBags : ∀ v : V, (T.induce ({w | v ∈ 𝓧 w})).Connected

variable {G : SimpleGraph V}

/-- Helper to build `connectedBags`: it suffices to exhibit, for each `v`, a bag
containing `v` together with preconnectedness of the induced subgraph. -/
lemma connectedBags_of_exists_mem {W : Type u} {𝓧 : W → Finset V} {T : SimpleGraph W}
    (h : ∀ v : V, (∃ w : W, v ∈ 𝓧 w) ∧ (T.induce ({w | v ∈ 𝓧 w})).Preconnected) :
    ∀ v : V, (T.induce ({w | v ∈ 𝓧 w})).Connected := fun v =>
  have ⟨w, hw⟩ := (h v).1
  have : Nonempty ({w | v ∈ 𝓧 w} : Set W) := ⟨⟨w, hw⟩⟩
  Connected.mk (h v).2


/-- The width of a tree decomposition: the maximum bag size minus one. -/
noncomputable def TreeDecomp.width (t : TreeDecomp G) : ℕ∞ :=
  ⨆ w : t.W, (#(t.𝓧 w) - 1 : ℕ∞)

/-- `ℕ`-valued view of `TreeDecomp.width`, with junk value `0` when the width is `⊤`. -/
noncomputable def TreeDecomp.widthNat (t : TreeDecomp G) : ℕ := t.width.toNat

lemma TreeDecomp.coe_widthNat (t : TreeDecomp G) (h : t.width ≠ ⊤) :
    (t.widthNat : ℕ∞) = t.width := ENat.coe_toNat h

/-- The tree decomposition obtained by putting all vertices in one bag. -/
def trivialTreeDecomp [Nonempty V] [Fintype V] (G : SimpleGraph V) : G.TreeDecomp where
  W := ULift.{u} Unit
  𝓧 := fun _ => univ
  T := ⊥
  isTree := by exact IsTree.of_subsingleton
  edgeCover := by simp
  connectedBags := by
    apply connectedBags_of_exists_mem
    exact fun _ => ⟨by simp, by aesop_graph⟩

lemma width_trivialTreeDecomp [Nonempty V] [Fintype V] :
    (G.trivialTreeDecomp).width = (card V - 1 : ℕ) := by
  change ⨆ _ : ULift.{u} Unit, ((#(univ : Finset V) - 1 : ℕ) : ℕ∞) = _
  rw [iSup_const, card_univ]

/-- The tree decomposition of `⊥` with one singleton bag per vertex, indexed by
`V` and connected via a star graph rooted at an arbitrary vertex. -/
noncomputable def botTreeDecomp [Nonempty V] : (⊥ : SimpleGraph V).TreeDecomp where
  W := V
  𝓧 := fun x => {x}
  T := star (Classical.arbitrary V)
  isTree := star_isTree _
  edgeCover _ _ h := h.elim
  connectedBags := connectedBags_of_exists_mem fun v =>
    ⟨⟨v, Finset.mem_singleton.mpr rfl⟩, by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Set.mem_setOf_eq, Finset.mem_singleton] at ha hb
      subst ha; subst hb
      exact ⟨.nil⟩⟩

lemma width_botTreeDecomp [Nonempty V] : (botTreeDecomp (V := V)).width = 0 := by
  change ⨆ x : V, ((#({x} : Finset V) - 1 : ℕ) : ℕ∞) = 0
  simp

/-- On a finite vertex type, every tree decomposition has width at most `card V - 1`. -/
lemma TreeDecomp.width_le_card [Fintype V] (t : TreeDecomp G) :
    t.width ≤ card V - 1 :=
  iSup_le fun _ => by
    exact_mod_cast Nat.sub_le_sub_right (Finset.card_le_univ _) 1

@[simp]
lemma TreeDecomp.coe_widthNat_of_finite [Finite V] (t : TreeDecomp G) :
    t.widthNat = t.width := by
  have : Fintype V := Fintype.ofFinite V
  exact t.coe_widthNat (t.width_le_card.trans_lt (ENat.coe_lt_top _)).ne

/-- A tree decomposition with finite width. -/
structure FiniteTreeDecomp (G : SimpleGraph V) extends TreeDecomp G where
  /-- The width is not infinite. -/
  width_ne_top : toTreeDecomp.width ≠ ⊤

namespace FiniteTreeDecomp

/-- `ℕ`-valued width of a finite tree decomposition. -/
noncomputable def width (t : FiniteTreeDecomp G) : ℕ := t.toTreeDecomp.widthNat

@[simp]
lemma coe_width (t : FiniteTreeDecomp G) : t.width = t.toTreeDecomp.width :=
  t.toTreeDecomp.coe_widthNat t.width_ne_top

end FiniteTreeDecomp

/-- Any tree decomposition on a finite vertex type has finite width. -/
noncomputable def TreeDecomp.toFinite [Finite V] (t : TreeDecomp G) :
    FiniteTreeDecomp G :=
  have : Fintype V := Fintype.ofFinite V
  { t with width_ne_top := (t.width_le_card.trans_lt (ENat.coe_lt_top _)).ne }

end TreeDecomp

/-! ## Tree width -/

section TreeWidth

variable {G : SimpleGraph V}

/-- The tree width of a simple graph: the infimum of widths over all tree
decompositions, valued in `ℕ∞`. -/
noncomputable def treeWidth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ t : TreeDecomp G, t.width

/-- `ℕ`-valued view of `treeWidth`, with junk value `0` when the treewidth is `⊤`. -/
noncomputable def treeWidthNat (G : SimpleGraph V) : ℕ := G.treeWidth.toNat

@[simp]
lemma treeDecomp_imp_treeWidth_le (treeDecomp : G.TreeDecomp) : G.treeWidth ≤ treeDecomp.width :=
  iInf_le _ treeDecomp

@[simp]
lemma treeWidth_le_iff_exists_treeDecomp (k : ℕ) :
    G.treeWidth ≤ k ↔ ∃ t : TreeDecomp G, t.width ≤ k := by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ => (treeDecomp_imp_treeWidth_le t).trans ht⟩
  by_contra hc
  push Not at hc
  have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ G.treeWidth := by
    rw [Nat.cast_add_one]
    exact le_iInf fun t => (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr (hc t)
  exact absurd (h1.trans h) (by exact_mod_cast Nat.not_succ_le_self k)

lemma coe_treeWidthNat (h : G.treeWidth ≠ ⊤) :
    (G.treeWidthNat : ℕ∞) = G.treeWidth := ENat.coe_toNat h

/-- The treewidth of a finite graph is at most `card V - 1`. -/
theorem treeWidth_le_card [Nonempty V] [Fintype V] :
    G.treeWidth ≤ card V - 1 :=
  (treeDecomp_imp_treeWidth_le G.trivialTreeDecomp).trans width_trivialTreeDecomp.le

@[simp]
lemma coe_treeWidthNat_of_finite [Finite V] [Nonempty V] :
    (G.treeWidthNat : ℕ∞) = G.treeWidth := by
  have : Fintype V := Fintype.ofFinite V
  exact coe_treeWidthNat (treeWidth_le_card.trans_lt (ENat.coe_lt_top _)).ne

/-- Nat-valued version of `treeWidth_le_card`. -/
theorem treeWidthNat_le_card [Nonempty V] [Fintype V] :
    G.treeWidthNat ≤ card V - 1 := by
  have h := treeWidth_le_card (G := G)
  rw [← coe_treeWidthNat_of_finite] at h
  exact_mod_cast h

/-- The treewidth of a graph is nonzero iff it has an edge. -/
theorem treeWidth_nonzero_iff_ne_bot [Nonempty V] : 0 < G.treeWidth ↔ G ≠ ⊥ := by
  classical
  rw [SimpleGraph.ne_bot_iff_exists_adj]
  constructor
  · contrapose!
    intro hAdj
    have hG : G = ⊥ := SimpleGraph.ext (by ext u v; simpa using hAdj u v)
    subst hG
    exact (treeDecomp_imp_treeWidth_le botTreeDecomp).trans width_botTreeDecomp.le
  · rintro ⟨u, v, huv⟩
    rw [← not_le]
    intro hle
    obtain ⟨t, ht⟩ := (treeWidth_le_iff_exists_treeDecomp 0).mp hle
    obtain ⟨w, hu, hv⟩ := t.edgeCover u v huv
    have h2 : 2 ≤ #(t.𝓧 w) := by
      have hsub : ({u, v} : Finset V) ⊆ t.𝓧 w := by
        simp [Finset.insert_subset_iff, hu, hv]
      exact (Finset.card_pair huv.ne).symm.trans_le (Finset.card_le_card hsub)
    -- The bag at `w` has size ≥ 2, so it contributes ≥ 1 to the supremum.
    have hbag : (1 : ℕ∞) ≤ (#(t.𝓧 w) - 1 : ℕ∞) := by
      exact_mod_cast show 1 ≤ #(t.𝓧 w) - 1 by omega
    have hw : (1 : ℕ∞) ≤ t.width :=
      hbag.trans (le_iSup (fun w => (#(t.𝓧 w) - 1 : ℕ∞)) w)
    exact absurd (hw.trans ht) (by decide)

end TreeWidth

end SimpleGraph
