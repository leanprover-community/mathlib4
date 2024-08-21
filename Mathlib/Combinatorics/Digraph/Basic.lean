/-
Copyright (c) 2024 Kyle Miller, Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jeremy Tan
-/
import Mathlib.Data.Set.Finite

/-!
# Digraphs

This file defines directed graphs on a vertex type `V`. The intention is to develop the notion
using the language of graph theory; furthermore, `Digraph` is not intended to be used as a class.

## Main definitions

* `Digraph` is a structure for arbitrary relations.
* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

open Finset Function

/-- A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which ordered pairs of vertices are adjacent. -/
@[ext]
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop

/-- Constructor for digraphs using a boolean function. -/
@[simps]
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨(x · ·)⟩
  inj' _ _ := by
    simp only [mk.injEq]; intro h; ext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr_fun₂ h v w

/-- We can enumerate digraphs by enumerating all functions `V → V → Bool`. -/
instance {V : Type*} [Fintype V] [DecidableEq V] : Fintype (Digraph V) :=
  Fintype.ofBijective Digraph.mk' <| by
    refine ⟨Embedding.injective _, ?_⟩
    classical
    intro G
    use fun v w ↦ G.Adj v w
    ext v w
    simp

/-- The digraph with all edges on a given vertex type `V`, denoted as `⊤`. -/
def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

/-- The digraph with no edges on a given vertex type `V`, denoted as `⊥`. -/
def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

namespace Digraph

variable {ι : Sort*} {V : Type*} (G H : Digraph V) (v w : V)

theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := fun _ _ ↦ Digraph.ext

@[simp] theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H := adj_injective.eq_iff

section Order

/-- The relation that one `Digraph` is a subgraph of another, denoted as `≤`. -/
def IsSubgraph : Prop := ∀ ⦃v w : V⦄, G.Adj v w → H.Adj v w

instance : LE (Digraph V) := ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The supremum of two digraphs `G ⊔ H` has edges where either `G` or `H` have edges. -/
instance : Sup (Digraph V) where sup x y := ⟨x.Adj ⊔ y.Adj⟩

@[simp] theorem sup_adj : (G ⊔ H).Adj v w ↔ G.Adj v w ∨ H.Adj v w := Iff.rfl

/-- The infimum of two digraphs `G ⊓ H` has edges where both `G` and `H` have edges. -/
instance : Inf (Digraph V) where inf G H := ⟨G.Adj ⊓ H.Adj⟩

@[simp] theorem inf_adj : (G ⊓ H).Adj v w ↔ G.Adj v w ∧ H.Adj v w := Iff.rfl

/-- The complement of a digraph `Gᶜ` has edges where `G` does not and vice versa. -/
instance : HasCompl (Digraph V) where compl G := ⟨(¬G.Adj · ·)⟩

@[simp] theorem compl_adj : Gᶜ.Adj v w ↔ ¬G.Adj v w := Iff.rfl

/-- The difference of two digraphs `G \ H` has the edges of `G` with the edges of `H` removed. -/
instance : SDiff (Digraph V) where sdiff G H := ⟨G.Adj \ H.Adj⟩

@[simp] theorem sdiff_adj : (G \ H).Adj v w ↔ G.Adj v w ∧ ¬H.Adj v w := Iff.rfl

instance : SupSet (Digraph V) where sSup s := ⟨fun a b ↦ ∃ G ∈ s, G.Adj a b⟩
instance : InfSet (Digraph V) where sInf s := ⟨fun a b ↦ ∀ G ∈ s, G.Adj a b⟩

@[simp]
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj v w ↔ ∃ G ∈ s, G.Adj v w := Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj v w ↔ ∀ G ∈ s, G.Adj v w := Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj v w ↔ ∃ i, (f i).Adj v w := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj v w ↔ ∀ i, (f i).Adj v w := by simp [iInf]

/-- For digraphs `G, H`, `G ≤ H` iff `∀ v w, G.Adj v w → H.Adj v w`. -/
instance distribLattice : DistribLattice (Digraph V) :=
  adj_injective.distribLattice _ (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) where
  __ := Digraph.distribLattice
  le := (· ≤ ·)
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  compl := HasCompl.compl
  sdiff := (· \ ·)
  top := completeDigraph V
  bot := emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  sdiff_eq _ _ := by ext; exact Iff.rfl
  top_le_sup_compl _ _ _ _ := by tauto
  inf_compl_le_bot _ _ _ h := (h.2 h.1).elim
  sSup := sSup
  le_sSup _ _ hG _ _ hA := ⟨_, hG, hA⟩
  sSup_le _ _ hG _ _ := by rintro ⟨_, hH, hA⟩; exact hG _ hH hA
  sInf := sInf
  sInf_le _ _ hG _ _ hA := hA _ hG
  le_sInf _ _ hG _ _ hA _ hH := hG _ hH hA
  iInf_iSup_eq _ := by ext; simp [Classical.skolem]

@[simp] theorem top_adj : (⊤ : Digraph V).Adj v w := trivial
@[simp] theorem bot_adj : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl
@[simp] theorem completeDigraph_eq_top (V) : completeDigraph V = ⊤ := rfl
@[simp] theorem emptyDigraph_eq_bot (V) : emptyDigraph V = ⊥ := rfl

@[simps] instance (V) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) := ⟨inferInstance, fun _ ↦ by ext1; congr!⟩

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w

instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w

instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True

instance Compl.adjDecidable : DecidableRel Gᶜ.Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

section EdgeSet

/-- The edges of G consist of the ordered pairs of vertices related by `G.Adj`.
This is the order embedding; for the edge set of a particular graph, see `Digraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `Iff.rfl`.
(That is, `(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.) -/
def edgeSetEmbedding (V) : Digraph V ↪o Set (V × V) :=
  OrderEmbedding.ofMapLEIff (fun G ↦ {e | G.Adj e.1 e.2}) fun _ _ ↦
    ⟨fun h v w ↦ @h (v, w), fun h _ me ↦ h me⟩

variable {G H}

/-- `G.edgeSet` is the edge set of `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : Digraph V) : Set (V × V) := edgeSetEmbedding V G

@[simp] theorem mem_edgeSet : (v, w) ∈ G.edgeSet ↔ G.Adj v w := Iff.rfl

theorem edgeSet_inj : G.edgeSet = H.edgeSet ↔ G = H := (edgeSetEmbedding V).eq_iff_eq

@[simp]
theorem edgeSet_subset_edgeSet : edgeSet G ⊆ edgeSet H ↔ G ≤ H := (edgeSetEmbedding V).le_iff_le

@[simp]
theorem edgeSet_ssubset_edgeSet : edgeSet G ⊂ edgeSet H ↔ G < H := (edgeSetEmbedding V).lt_iff_lt

theorem edgeSet_injective : Injective (edgeSet : Digraph V → Set (V × V)) :=
  (edgeSetEmbedding V).injective

alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet
alias ⟨_, edgeSet_strictMono⟩ := edgeSet_ssubset_edgeSet
attribute [mono] edgeSet_mono edgeSet_strictMono

variable (G H)

@[simp] theorem edgeSet_bot : (⊥ : Digraph V).edgeSet = ∅ := rfl
@[simp] theorem edgeSet_top : (⊤ : Digraph V).edgeSet = Set.univ := rfl
@[simp] theorem edgeSet_sup : (G ⊔ H).edgeSet = G.edgeSet ∪ H.edgeSet := rfl
@[simp] theorem edgeSet_inf : (G ⊓ H).edgeSet = G.edgeSet ∩ H.edgeSet := rfl
@[simp] theorem edgeSet_sdiff : (G \ H).edgeSet = G.edgeSet \ H.edgeSet := rfl

variable {G H}

@[simp] lemma disjoint_edgeSet : Disjoint G.edgeSet H.edgeSet ↔ Disjoint G H := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edgeSet_inf, ← edgeSet_bot, ← Set.le_iff_subset,
    OrderEmbedding.le_iff_le]

@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]

@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]

variable (G H)

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  fun e ↦ ‹DecidableRel G.Adj› e.1 e.2

instance fintypeEdgeSet [Fintype V] [DecidableRel G.Adj] : Fintype G.edgeSet := by infer_instance

instance fintypeEdgeSetBot : Fintype (⊥ : Digraph V).edgeSet := by rw [edgeSet_bot]; infer_instance

variable [DecidableEq V] [Fintype G.edgeSet] [Fintype H.edgeSet]

instance fintypeEdgeSetSup : Fintype (G ⊔ H).edgeSet := by
  rw [edgeSet_sup]; infer_instance

instance fintypeEdgeSetInf : Fintype (G ⊓ H).edgeSet := by
  rw [edgeSet_inf]; exact Set.fintypeInter _ _

instance fintypeEdgeSetSDiff : Fintype (G \ H).edgeSet := by
  rw [edgeSet_sdiff]; exact Set.fintypeDiff _ _

end EdgeSet

end Digraph
