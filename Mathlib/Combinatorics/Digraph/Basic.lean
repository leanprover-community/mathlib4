/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
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
  left_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → v ∈ verts := by aesop
  /-- There is no edge of the digraph outside its vertices. -/
  right_mem_verts_of_adj ⦃v w : V⦄ : Adj v w → w ∈ verts := by aesop

namespace Digraph

attribute [aesop unsafe] left_mem_verts_of_adj right_mem_verts_of_adj

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
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


  -- Fintype.ofBijective Digraph.mk' <| by
  --    classical
  --    refine ⟨Embedding.injective _, ?_⟩

open Finset Set in
instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Set V) := inferInstanceAs Set.fintype

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where
  verts := ⊤
  Adj := ⊤

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges.
-/
protected def emptyDigraph (V : Type*) : Digraph V where
  Adj _ _ := False
  verts := ∅

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
def completeBipartite (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  verts := Set.univ

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

-- Note `adj_injective` is no longer true
-- theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := by
--   intro G₁ G₂ h
--   ext

@[simp] theorem adj_inj {G H : Digraph V} : verts G = verts H ∧ G.Adj = H.Adj  ↔ G = H :=
  Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : Max (Digraph V) where
  max x y := {
    verts := x.verts ⊔ y.verts
    Adj := x.Adj ⊔ y.Adj
  }

@[simp]
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : Min (Digraph V) where
  min x y := {
    verts := x.verts ⊓ y.verts
    Adj := x.Adj ⊓ y.Adj
  }

@[simp]
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
instance hasCompl : HasCompl (Digraph V) where
  compl G := {
    verts := G.verts
    Adj v w := v ∈ G.verts ∧ w ∈ G.verts ∧ ¬G.Adj v w
  }

@[simp] theorem compl_adj (G : Digraph V) (v w : V) (hmem : v ∈ G.verts ∧ w ∈ G.verts)
  : Gᶜ.Adj v w ↔ ¬G.Adj v w := by
  constructor
  · intro compl_adj
    simp only [hasCompl] at compl_adj
    tauto
  · intro adj
    simp only [hasCompl]
    tauto

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

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (Digraph V) where
    le := fun G H ↦  (G.verts ⊆ H.verts) ∧ (∀ ⦃v w⦄, G.Adj v w → H.Adj v w)
    le_refl := by
      intro G
      tauto
    le_trans := by
      intro G₁ G₂ G₃ h₁₂ h₂₃
      tauto
    le_antisymm := by
      intro G H h h'
      ext v w <;> tauto
    sup := max
    inf := min
    le_sup_left := by
      intro G H
      constructor
      · simp only [max, SemilatticeSup.sup, Set.subset_union_left]
      · intro v w adj
        simp only [max, SemilatticeSup.sup]
        left; assumption
    le_sup_right := by
      intro G H
      constructor
      · simp only [max, SemilatticeSup.sup, Set.subset_union_right]
      · intro v w adj
        simp only [max, SemilatticeSup.sup]
        right; assumption

    inf_le_left := by
      intro G H
      constructor
      · simp only [min, SemilatticeInf.inf, Lattice.inf, Set.inter_subset_left]
      · intro v w adj
        simp only [min, SemilatticeInf.inf, Lattice.inf] at adj
        tauto

    inf_le_right := by
      intro G H
      constructor
      · simp only [min, SemilatticeInf.inf, Lattice.inf, Set.inter_subset_right]
      · intro v w adj
        simp only [min, SemilatticeInf.inf, Lattice.inf] at adj
        tauto

    sup_le := by
      intro G H supG hG hH
      constructor
      · simp only [max, SemilatticeSup.sup, Set.union_subset_iff]
        tauto
      · simp only [max, SemilatticeSup.sup]
        tauto

    le_inf := by
      intro G H infG hG hH
      constructor
      · simp only [min, SemilatticeInf.inf, Lattice.inf, Set.subset_inter_iff]
        tauto
      · simp only [min, SemilatticeInf.inf, Lattice.inf]
        tauto

    le_sup_inf := by
      intro G H I
      simp only [min, SemilatticeInf.inf,
        Lattice.inf, max, SemilatticeSup.sup, and_imp]
      constructor
      · rw [←Set.union_inter_distrib_left]
      · intro v w hGH gGI
        tauto

abbrev spanningLE (H : Digraph V) (G : Digraph V) : Prop :=
  distribLattice.le H G ∧ H.verts = G.verts


abbrev spanningSubgraph_compl (H G : Digraph V) : Digraph V where
  verts := G.verts
  Adj v w := ¬ H.Adj v w ∧ v ∈ G.verts ∧ w ∈ G.verts ∧ G.Adj v w

lemma spanningSubgraph_compl_subgraph (H G : Digraph V) :
  distribLattice.le (spanningSubgraph_compl H G) G := by
  unfold spanningSubgraph_compl
  simp [LE.le]


section SpanningSubgraphs

/-!
In this section we provide the complete boolean algebra for spanning subgraphs
-/

abbrev SpanningSubgraph (G : Digraph V) := {H : Digraph V // H ≤ G ∧ H.verts = G.verts}




def sup {G : Digraph V} (H₁ H₂ : G.SpanningSubgraph) : G.SpanningSubgraph := by
  obtain ⟨H₁, H₁_sub, H₁_verts_eq⟩ := H₁
  obtain ⟨H₂, H₂_sub, H₂_verts_eq⟩ := H₂
  constructor
  case val =>
    exact (max H₁ H₂)
  case property =>
    simp_all only [LE.le, max, SemilatticeSup.sup, Set.union_self, and_true]
    constructor
    · rintro v h
      simp only at h
      exact h
    · intro v w adj
      simp only at adj
      obtain (hH₁ |hH₂) := adj
      · apply H₁_sub.right hH₁
      · apply H₂_sub.right hH₂

def top {G : Digraph V} : G.SpanningSubgraph := ⟨G, by simp⟩

def compl {G : Digraph V} (H : G.SpanningSubgraph) : G.SpanningSubgraph := by
  constructor
  case val => exact {
    verts := H.val.verts
    Adj v w := G.Adj v w ∧ ¬ H.val.Adj v w ∧ v ∈ H.val.verts ∧ w ∈ H.val.verts
  }
  case property =>
    simp_all only [H.property, and_true]
    unfold instLE LE.le Digraph.IsSubgraph
    simp only [subset_refl, and_imp, true_and]
    intro v w G_adj H_adj _ _
    assumption

def inf {G : Digraph V} (H₁ H₂ : G.SpanningSubgraph) : G.SpanningSubgraph := by
  constructor
  case val => exact (min H₁.val H₂.val)
  case property =>
    obtain ⟨H₁, ⟨H₁_sub, H₁_verts⟩⟩ := H₁
    obtain ⟨H₂, ⟨H₂_sub, H₂_verts⟩⟩ := H₂
    constructor
    · simp_all only [min, SemilatticeInf.inf, Lattice.inf, Set.inter_self]
      unfold instLE LE.le Digraph.IsSubgraph
      simp only [subset_refl, and_imp, true_and]
      intro v w H₁_adj H₂_adj
      apply H₂_sub.right
      exact H₂_adj
    · simp only [min, SemilatticeInf.inf, Lattice.inf]
      rw [H₁_verts, H₂_verts]
      simp only [Set.inter_self]


def bot {G : Digraph V} : G.SpanningSubgraph where
  val :=
    ⟨G.verts, fun _ _ => False, by simp, by simp⟩
  property := by
    unfold instLE LE.le Digraph.IsSubgraph
    simp only [subset_refl, IsEmpty.forall_iff, implies_true, and_self]

lemma le_sup_left {G : Digraph V} : ∀ H₁ H₂ : G.SpanningSubgraph, H₁ ≤ (sup H₁ H₂) := by
  intro ⟨H₁, H₁_sub, H₁_verts⟩ ⟨H₂, H₂_sub, H₂_verts⟩
  unfold instLE LE.le Digraph.IsSubgraph Subtype.instLE
  simp only [sup, max, SemilatticeSup.sup, Set.subset_union_left, true_and]
  intro _ _ h
  tauto

lemma le_sup_right {G : Digraph V} : ∀ H₁ H₂ : G.SpanningSubgraph, H₂ ≤ (sup H₁ H₂) := by
  intro ⟨H₁, H₁_sub, H₁_verts⟩ ⟨H₂, H₂_sub, H₂_verts⟩
  unfold instLE LE.le Digraph.IsSubgraph Subtype.instLE
  simp only [sup, max, SemilatticeSup.sup, Set.subset_union_right, true_and]
  intro _ _ h
  tauto

lemma sup_le {G : Digraph V} : ∀ H₁ H₂ H₃ : G.SpanningSubgraph,
  H₁ ≤ H₃ → H₂ ≤ H₃ → sup H₁ H₂ ≤ H₃ := by
  intro ⟨H₁, ⟨H₁_sub, H₁_verts⟩⟩ ⟨H₂, ⟨H₂_sub, H₂_verts⟩⟩ ⟨H₃, ⟨H₃_sub, H₃_verts⟩⟩
  simp_all [sup]

lemma inf_le_left {G : Digraph V} : ∀ H₁ H₂ : G.SpanningSubgraph,
  inf H₁ H₂ ≤ H₁ := by
  intro ⟨H₁, ⟨H₁_sub, H₁_verts⟩⟩ ⟨H₂, ⟨H₂_sub, H₂_verts⟩⟩
  simp_all [inf]

lemma inf_le_right {G : Digraph V} : ∀ H₁ H₂ : G.SpanningSubgraph,
  inf H₁ H₂ ≤ H₂ := by
  intro ⟨H₁, ⟨H₁_sub, H₁_verts⟩⟩ ⟨H₂, ⟨H₂_sub, H₂_verts⟩⟩
  simp_all [inf]

lemma le_inf {G : Digraph V} : ∀ H₁ H₂ H₃ : G.SpanningSubgraph,
  H₁ ≤ H₂ → H₁ ≤ H₃ → H₁ ≤ inf H₂ H₃ := by
  intro ⟨H₁, ⟨H₁_sub, H₁_verts⟩⟩ ⟨H₂, ⟨H₂_sub, H₂_verts⟩⟩ ⟨H₃, ⟨H₃_sub, H₃_verts⟩⟩
  simp_all [inf]

lemma le_top {G : Digraph V} : ∀ H : G.SpanningSubgraph,
  H ≤ top := by
  intro ⟨H, ⟨H_sub, H_verts⟩⟩
  simp_all [top]

lemma bot_le {G : Digraph V} : ∀ (H : G.SpanningSubgraph), bot ≤ H := by
  intro ⟨H, ⟨H_sub, H_verts⟩⟩
  unfold instLE LE.le Subtype.instLE
  simp_all [Digraph.IsSubgraph, bot]


def sSup {G : Digraph V} (ℋ : Set G.SpanningSubgraph) : G.SpanningSubgraph where
  val := {
    verts :=  G.verts,
    Adj v w := ∃ H ∈ ℋ, Adj H.val v w
    left_mem_verts_of_adj := by
      simp_all only [SpanningSubgraph, Subtype.exists, exists_and_right, forall_exists_index,
        and_imp, forall_and_index]
      intro v w H H_sub H_verts H_mem H_adj
      apply H_sub.right at H_adj
      apply G.left_mem_verts_of_adj H_adj
    right_mem_verts_of_adj := by
      simp_all only [SpanningSubgraph, Subtype.exists, exists_and_right, forall_exists_index,
        and_imp, forall_and_index]
      intro v w H H_sub H_verts H_mem H_adj
      apply H_sub.right at H_adj
      apply G.right_mem_verts_of_adj H_adj
  }
  property := by
    constructor
    · simp_all only [Subtype.exists, exists_and_right]
      constructor
      · simp only [subset_refl]
      · intro v w ⟨H, ⟨⟨H_sub, H_verts⟩,H_mem⟩, H_adj⟩
        apply H_sub.right at H_adj
        exact H_adj
    · simp only

def sInf {G : Digraph V} (ℋ : Set G.SpanningSubgraph) : G.SpanningSubgraph where
  val := {
    verts := G.verts
    Adj v w := (∃ H, H ∈ ℋ) ∧ ∀ H ∈ ℋ, Adj H.val v w
    left_mem_verts_of_adj := by
      intro v w ⟨⟨⟨H, ⟨H_sub, H_verts⟩⟩, h_mem⟩, h_forall⟩
      specialize h_forall ⟨H, ⟨H_sub, H_verts⟩⟩ h_mem
      simp_all only [SpanningSubgraph]
      apply H_sub.right at h_forall
      apply G.left_mem_verts_of_adj h_forall
    right_mem_verts_of_adj := by
      intro v w ⟨⟨⟨H, ⟨H_sub, H_verts⟩⟩, h_mem⟩, h_forall⟩
      specialize h_forall ⟨H, ⟨H_sub, H_verts⟩⟩ h_mem
      simp_all only [SpanningSubgraph]
      apply H_sub.right at h_forall
      apply G.right_mem_verts_of_adj h_forall
  }
  property := by
    constructor
    · constructor
      · simp
      · simp only [Subtype.forall, forall_and_index]
        intro v w ⟨⟨H, ⟨H_sub, H_verts⟩⟩, H_mem⟩ h
        specialize h H H_sub H_verts H_mem
        apply H_sub.right at h
        assumption
    · simp


lemma le_sSup {G : Digraph V} : ∀ (ℋ : Set G.SpanningSubgraph), ∀ H ∈ ℋ, H ≤ sSup ℋ := by
  intro ℋ ⟨H, ⟨H_sub, H_verts⟩⟩ H_mem
  constructor
  · simp_all [sSup]
  · simp_all only [sSup, Subtype.exists, exists_and_right]
    intro v w H_adj
    tauto

lemma sSup_le {G : Digraph V} : ∀ (ℋ : Set G.SpanningSubgraph)
  (H : G.SpanningSubgraph), (∀ H' ∈ ℋ, H' ≤ H) → sSup ℋ ≤ H := by
  intro ℋ ⟨H, ⟨H_verts, H_adj⟩, H_verts_eq⟩ H'
  constructor
  · simp only [sSup, Subtype.exists, exists_and_right]
    rw [H_verts_eq]
  · intro v w ⟨Hs, Hs_mem, Hs_adj⟩
    specialize H' Hs Hs_mem
    apply H'.right at Hs_adj
    assumption

lemma top_le_sup_compl {G : Digraph V} : ∀ (H : G.SpanningSubgraph), top ≤ sup H (compl H) := by
  intro ⟨H, H_sub, H_verts⟩
  constructor
  · simp only [top, sup, compl, max, SemilatticeSup.sup, Set.union_self, Set.subset_def]
    intro v v_in_G
    grind
  · intro v w top_adj
    simp only [top] at top_adj
    simp_all [sup, max, SemilatticeSup.sup]
    sorry

lemma sInf_le {G : Digraph V} : ∀ (ℋ : Set G.SpanningSubgraph),
  ∀ H ∈ ℋ, sInf ℋ ≤ H := by
  intro ℋ ⟨H, ⟨H_sub, H_verts_eq⟩⟩ H_mem
  constructor
  · simp only [sInf, Subtype.exists, Subtype.forall, forall_and_index]
    rw [H_verts_eq]
  · intro v w adj
    simp_all [sInf]

lemma le_sInf {G : Digraph V} : ∀ (ℋ : Set G.SpanningSubgraph)
  (H : G.SpanningSubgraph), (∀ H' ∈ ℋ, H ≤ H') → H ≤ sInf ℋ := by
  intro ℋ ⟨H, ⟨H_sub, H_verts⟩⟩ h_sub
  constructor
  · simp_all [sInf]
  · intro v w h_adj
    simp_all only [Subtype.forall, Subtype.mk_le_mk, forall_and_index, sInf, Subtype.exists]
    constructor
    · use H, ⟨H_sub, H_verts⟩
      
      sorry
      done
    · intro a ha hv hmem
      specialize h_sub a ha hv hmem
      apply h_sub.right at h_adj
      assumption

noncomputable instance (G : Digraph V) : CompleteBooleanAlgebra
  (G.SpanningSubgraph) where
  sup := sup
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := sup_le
  inf := inf
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf
  top := top
  le_top := le_top
  bot := bot
  bot_le := bot_le
  compl := compl
  sSup := sSup
  sInf := sInf
  le_sSup := le_sSup
  sSup_le := sSup_le
  top_le_sup_compl := top_le_sup_compl
  sInf_le := sInf_le
  le_sInf := le_sInf
  le_sup_inf := by
    intro ⟨H₁, hH₁⟩ ⟨H₂, hH₂⟩ ⟨H₃, hH₃⟩
    constructor
    · simp_all [max, min, inf, SemilatticeInf.inf, Lattice.inf, sup,
        SemilatticeSup.sup]
      grind
    · intro v w adj
      simp_all [max, min, inf, SemilatticeInf.inf, Lattice.inf,
      sup, SemilatticeSup.sup]
      sorry

  inf_compl_le_bot := by
    intro ⟨H, H_prop⟩
    simp only [min, SemilatticeInf.inf, inf, Lattice.inf, ge_iff_le]
    constructor
    · simp [compl, bot, H_prop]
    · simp only [compl, H_prop, bot, imp_false, not_and]
      intro v w H_adj G_adj not_H_adj v_verts
      exfalso
      exact (ne_self_iff_false a).mp fun a ↦ not_H_adj H_adj

#exit




end SpanningSubgraphs




@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl

@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := by
  simp [Digraph.completeDigraph]


@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

instance [iE : IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by
    ext1
    · sorry
    · congr!

instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

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

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

end Digraph
