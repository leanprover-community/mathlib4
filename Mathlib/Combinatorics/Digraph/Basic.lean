/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan, Shreyas Srinivas
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`,
which is the same notion as a relation `V → V → Prop`.
While this might be too simple of a notion to deserve the grandeur of a new definition,
the intention here is to develop relations using the language of graph theory.

Note that in this treatment, a digraph may have self loops.

The type `Digraph V` is structurally equivalent to `Quiver.{0} V`,
but a difference between these is that `Quiver` is a class —
its purpose is to attach a quiver structure to a particular type `V`.
In contrast, for `Digraph V` we are interested in working with the entire lattice
of digraphs on `V`.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

@[expose] public section

open Finset Function

/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
@[ext]
structure Digraph (V : Type*) where
  /-- The vertex set of a digraph. -/
  verts : Set V
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop
  /-- There is no edge of the digraph outside its vertices. -/
  left_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → v ∈ verts := by grind
  /-- There is no edge of the digraph outside its vertices. -/
  right_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → w ∈ verts := by grind

namespace Digraph

attribute [grind →] left_mem_verts_of_adj right_mem_verts_of_adj

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation.
-/
@[simps]
def mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := {
    verts := {v | ∃ w, x v w ∨ x w v}
    Adj v w := x v w
  }
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro ⟨_, h⟩
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where
  verts := .univ
  Adj := ⊤

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that there are no vertices and therefore no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges and no vertices.
-/
protected def emptyDigraph (V : Type*) : Digraph V where
  verts := ∅
  Adj _ _ := False

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
def completeBipartite (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  verts := Set.univ

/-- Deprecated alias for `completeBipartite`. -/
@[deprecated completeBipartite (since := "2026-09-01")]
abbrev completeBipartiteGraph := completeBipartite

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

@[simp] theorem adj_inj {G H : Digraph V} : verts G = verts H ∧ G.Adj = H.Adj ↔ G = H :=
  Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The relation that one `Digraph` is a spanning subgraph of another. -/
def IsSpanningSubgraph (x y : Digraph V) : Prop :=
  x ≤ y ∧ x.verts = y.verts
@[grind =] theorem isSpanningSubgraph_iff {x y : Digraph V} :
    IsSpanningSubgraph x y ↔ x ≤ y ∧ x.verts = y.verts := by
  rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (Digraph V) where
  max x y := {
    verts := x.verts ∪ y.verts
    Adj v w := x.Adj v w ∨ y.Adj v w
  }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (Digraph V) where
  min x y := {
    verts := x.verts ∩ y.verts
    Adj v w := x.Adj v w ∧ y.Adj v w
  }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance : Compl (Digraph V) where
  compl G := {
    verts := G.verts
    Adj v w := v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w
  }

@[simp] theorem compl_adj (G : Digraph V) (v w : V) (hv : v ∈ G.verts) (hw : w ∈ G.verts) :
  Gᶜ.Adj v w ↔ ¬G.Adj v w := ⟨fun h => h.2.2, fun h => ⟨hv, hw, h⟩⟩

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := {
    verts := x.verts
    Adj v w := x.Adj v w ∧ ¬ y.Adj v w
  }

@[simp]
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := Iff.rfl

instance supSet : SupSet (Digraph V) where
  sSup s := {
    verts := {v | ∃ G ∈ s, v ∈ G.verts}
    Adj v w := ∃ G ∈ s, Adj G v w
  }

instance infSet : InfSet (Digraph V) where
  sInf s := {
    verts := {v | ∀ G ∈ s, v ∈ G.verts}
    Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b)
  }

@[simp]
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b := Iff.rfl

@[simp]
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]

instance : LT (Digraph V) where
  lt G H := G ≤ H ∧ ¬H ≤ G

instance distribLattice : DistribLattice (Digraph V) :=
  fast_instance% Function.Injective.distribLattice (fun G ↦ (G.verts, G.Adj))
    (fun _ _ h ↦ Digraph.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

@[simp] theorem isSpanningSubgraph_self (G : Digraph V) : IsSpanningSubgraph G G := by
  simp [isSpanningSubgraph_iff]


section SpanningSubgraphs

/-!
In this section we provide the complete boolean algebra for spanning subgraphs
-/

/--
The type of spanning subgraphs of a digraph `G`
-/
def SpanningSubgraph (G : Digraph V) := {H : Digraph V // IsSpanningSubgraph H G}

instance {G : Digraph V} : PartialOrder G.SpanningSubgraph where
  le H K := H.val ≤ K.val
  le_refl H := by
    constructor
    · intro v hv; exact hv
    · intro v w h; exact h
  le_trans H K L hHK hKL := hHK.trans hKL
  le_antisymm H K hHK hKH := by
    apply Subtype.ext
    exact le_antisymm hHK hKH

@[simp] theorem SpanningSubgraph.le_iff_val_le {G : Digraph V}
    {H K : G.SpanningSubgraph} :
    H ≤ K ↔ H.val ≤ K.val := by
  rfl

@[simp] theorem SpanningSubgraph.mk_le_mk {G H K : Digraph V}
    {hH : IsSpanningSubgraph H G} {hK : IsSpanningSubgraph K G} :
    (⟨H, hH⟩ : G.SpanningSubgraph) ≤ ⟨K, hK⟩ ↔ H ≤ K := by
  rfl

@[simp] theorem SpanningSubgraph.property_le {G : Digraph V}
    (H : G.SpanningSubgraph) :
    H.val ≤ G := by
  exact (isSpanningSubgraph_iff.mp H.property).1

@[simp] theorem SpanningSubgraph.property_verts {G : Digraph V}
    (H : G.SpanningSubgraph) :
    H.val.verts = G.verts := by
  exact (isSpanningSubgraph_iff.mp H.property).2

/-- The adjacency relation of a spanning subgraph, restricted to the edges of the ambient
digraph. -/
@[simp] def SpanningSubgraph.Adj {G : Digraph V} (H : G.SpanningSubgraph) :
    ({e : V × V // G.Adj e.1 e.2} → Prop) := fun e ↦ H.val.Adj e.1.1 e.1.2

/-- The join/union of two spanning subgraphs. -/
instance {G : Digraph V} : Max G.SpanningSubgraph where
  max H₁ H₂ := by
    constructor
    case val => exact max H₁.val H₂.val
    case property =>
      have h₁verts : H₁.val.verts = G.verts := H₁.property.2
      have h₂verts : H₂.val.verts = G.verts := H₂.property.2
      constructor
      · simpa [max, SemilatticeSup.sup] using
          (show H₁.val ⊔ H₂.val ≤ G from _root_.sup_le H₁.property.1 H₂.property.1)
      · aesop (add simp [max, SemilatticeSup.sup, h₁verts, h₂verts])

@[push_cast]
lemma sup_of_val {G : Digraph V} (H₁ H₂ : G.SpanningSubgraph) :
  (H₁ ⊔ H₂).val = H₁.val ⊔ H₂.val := rfl

/--
The top subgraph `⊤`
-/
instance {G : Digraph V} : OrderTop G.SpanningSubgraph where
  top : G.SpanningSubgraph := ⟨G, by aesop⟩
  le_top := by
    intro ⟨H, ⟨H_sub, H_verts⟩⟩
    simp_all

/--
The bottom subgraph `⊥`
-/
instance {G : Digraph V} : OrderBot G.SpanningSubgraph where
  bot : G.SpanningSubgraph := ⟨
    ⟨G.verts, fun _ _ => False, by simp, by simp⟩,
    by
      rw [isSpanningSubgraph_iff]
      constructor
      · constructor
        · intro v hv
          exact hv
        · intro v w h
          exact False.elim h
      · rfl⟩
  bot_le := by
    intro H
    constructor
    · intro v hv
      simpa [SpanningSubgraph.property_verts H] using hv
    · intro v w h
      exact False.elim h

/-- The complement of a spanning subgraph with respect to its ambient digraph. -/
instance {G : Digraph V} : Compl G.SpanningSubgraph where
  compl H := by
    constructor
    case val => exact {
      verts := H.val.verts
      Adj v w := G.Adj v w ∧ ¬H.val.Adj v w
    }
    case property =>
      constructor
      · constructor
        · intro v hv
          simpa [H.property.2] using hv
        · intro _ _ h
          exact h.1
      · simp

/-- The meet/intersection of two spanning subgraphs. -/
instance {G : Digraph V} : Min G.SpanningSubgraph where
  min H₁ H₂ := by
    constructor
    case val => exact min H₁.val H₂.val
    case property =>
      have h₁verts : H₁.val.verts = G.verts := H₁.property.2
      have h₂verts : H₂.val.verts = G.verts := H₂.property.2
      constructor
      · simpa [min, SemilatticeInf.inf, Lattice.inf] using
          (show H₁.val ⊓ H₂.val ≤ G from _root_.inf_le_left.trans H₁.property.1)
      · aesop (add simp [min, SemilatticeInf.inf, Lattice.inf, h₁verts, h₂verts])

@[push_cast]
lemma inf_of_val {G : Digraph V} (H₁ H₂ : G.SpanningSubgraph) :
  (H₁ ⊓ H₂).val = H₁.val ⊓ H₂.val := rfl

/-- The supremum of a set of spanning subgraphs. -/
instance {G : Digraph V} : SupSet G.SpanningSubgraph where
  sSup ℋ := {
    val := {
      verts := G.verts
      Adj v w := ∃ H ∈ ℋ, H.val.Adj v w
    }
    property := by
      constructor
      · constructor
        · simp
        · rintro v w ⟨H, -, hAdj⟩
          exact H.property.1.2 hAdj
      · rfl
  }

/-- The infimum of a set of spanning subgraphs. -/
instance {G : Digraph V} : InfSet G.SpanningSubgraph where
  sInf ℋ := {
    val := {
      verts := G.verts
      Adj v w := (∀ H ∈ ℋ, H.val.Adj v w) ∧ G.Adj v w
    }
    property := by
      constructor
      · constructor <;> aesop
      · rfl
  }

instance {G : Digraph V} : HImp G.SpanningSubgraph where
  himp H K := Hᶜ ⊔ K

instance {G : Digraph V} : SDiff G.SpanningSubgraph where
  sdiff H K := H ⊓ Kᶜ

@[simp] theorem SpanningSubgraph.sSup_val_adj {G : Digraph V} (s : Set G.SpanningSubgraph)
    (v w : V) : (sSup s).val.Adj v w ↔ ∃ H ∈ s, H.val.Adj v w := Iff.rfl

@[simp] theorem SpanningSubgraph.sInf_val_adj {G : Digraph V} (s : Set G.SpanningSubgraph)
    (v w : V) : (sInf s).val.Adj v w ↔
      (∀ H ∈ s, H.val.Adj v w) ∧ G.Adj v w := Iff.rfl

@[simp] theorem SpanningSubgraph.compl_val_adj {G : Digraph V} (H : G.SpanningSubgraph)
    (v w : V) : (Hᶜ).val.Adj v w ↔ G.Adj v w ∧ ¬H.val.Adj v w := Iff.rfl

@[simp] theorem SpanningSubgraph.himp_val_adj {G : Digraph V} (H K : G.SpanningSubgraph)
    (v w : V) : (H ⇨ K).val.Adj v w ↔
      (G.Adj v w ∧ ¬H.val.Adj v w) ∨ K.val.Adj v w := Iff.rfl

@[simp] theorem SpanningSubgraph.sdiff_val_adj {G : Digraph V} (H K : G.SpanningSubgraph)
    (v w : V) : (H \ K).val.Adj v w ↔
      H.val.Adj v w ∧ (G.Adj v w ∧ ¬K.val.Adj v w) := Iff.rfl

theorem SpanningSubgraph.adj_le_iff {G : Digraph V} {H K : G.SpanningSubgraph} :
    SpanningSubgraph.Adj H ≤ SpanningSubgraph.Adj K ↔ H ≤ K := by
  constructor
  · intro h
    rw [SpanningSubgraph.le_iff_val_le]
    constructor
    · intro v hv
      rw [SpanningSubgraph.property_verts K]
      rwa [SpanningSubgraph.property_verts H] at hv
    · intro v w hvw
      have hG : G.Adj v w := (SpanningSubgraph.property_le H).2 hvw
      exact h ⟨(v, w), hG⟩ hvw
  · intro h e he
    exact h.2 he

theorem SpanningSubgraph.adj_injective {G : Digraph V} :
    Function.Injective (SpanningSubgraph.Adj (G := G)) := by
  intro H K h
  apply le_antisymm
  · exact SpanningSubgraph.adj_le_iff.mp h.le
  · exact SpanningSubgraph.adj_le_iff.mp h.ge

@[simp] theorem SpanningSubgraph.adj_sSup {G : Digraph V} (s : Set G.SpanningSubgraph) :
    SpanningSubgraph.Adj (sSup s) = ⨆ H ∈ s, SpanningSubgraph.Adj H := by
  funext e
  apply propext
  simp

@[simp] theorem SpanningSubgraph.adj_sInf {G : Digraph V} (s : Set G.SpanningSubgraph) :
    SpanningSubgraph.Adj (sInf s) = ⨅ H ∈ s, SpanningSubgraph.Adj H := by
  funext e
  apply propext
  simp [e.2]

@[simp] theorem SpanningSubgraph.adj_top {G : Digraph V} :
    SpanningSubgraph.Adj (⊤ : G.SpanningSubgraph) = ⊤ := by
  funext e
  apply propext
  exact iff_true_intro e.2

@[simp] theorem SpanningSubgraph.adj_compl {G : Digraph V} (H : G.SpanningSubgraph) :
    SpanningSubgraph.Adj Hᶜ = (SpanningSubgraph.Adj H)ᶜ := by
  funext e
  apply propext
  simp [Pi.compl_apply, e.2]

@[simp] theorem SpanningSubgraph.adj_himp {G : Digraph V} (H K : G.SpanningSubgraph) :
    SpanningSubgraph.Adj (H ⇨ K) = SpanningSubgraph.Adj H ⇨ SpanningSubgraph.Adj K := by
  funext e
  apply propext
  simp [Pi.himp_apply, himp_eq, e.2, or_comm]

@[simp] theorem SpanningSubgraph.adj_sdiff {G : Digraph V} (H K : G.SpanningSubgraph) :
    SpanningSubgraph.Adj (H \ K) = SpanningSubgraph.Adj H \ SpanningSubgraph.Adj K := by
  funext e
  apply propext
  simp [Pi.sdiff_apply, sdiff_eq, e.2]

instance (G : Digraph V) : CompleteBooleanAlgebra G.SpanningSubgraph :=
  fast_instance% Function.Injective.completeBooleanAlgebra SpanningSubgraph.Adj
    SpanningSubgraph.adj_injective SpanningSubgraph.adj_le_iff
      (by
        intro H K
        rw [lt_iff_le_not_ge, lt_iff_le_not_ge, SpanningSubgraph.adj_le_iff,
          SpanningSubgraph.adj_le_iff])
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) SpanningSubgraph.adj_sSup
      SpanningSubgraph.adj_sInf SpanningSubgraph.adj_top (by rfl)
      SpanningSubgraph.adj_compl SpanningSubgraph.adj_himp SpanningSubgraph.adj_sdiff

end SpanningSubgraphs

instance Top : Top (Digraph V) where
  top := Digraph.completeDigraph V

instance Bot : Bot (Digraph V) where
  bot := Digraph.emptyDigraph V

@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl

@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl

@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by
    ext1
    · rw [← Digraph.emptyDigraph_eq_bot, Set.eq_empty_of_isEmpty G.verts]
      rfl
    · congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
variable [DecidablePred (· ∈ G.verts)] [DecidablePred (· ∈ H.verts)]

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

instance decidableRelAdjCompl : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦
    v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w

end Decidable

end Order

end Digraph
