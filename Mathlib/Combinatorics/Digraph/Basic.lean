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
The relation that one `Digraph` is a spanning subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

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




instance (G : Digraph V) : CompleteBooleanAlgebra (Set.Iic G) where
  sup H₁ H₂ := by
    cases H₁ with | mk H₁ H₁_prop
    cases H₂ with | mk H₂ H₂_prop
    constructor
    case val =>
      exact (max H₁ H₂)
    case property =>
      simp_all
  le_sup_left := by
    intro a b
    simp_all only
    apply distribLattice.le_sup_left
  le_sup_right := by
    intro a b
    simp_all only
    apply distribLattice.le_sup_right
  sup_le := by
    intro a b c
    simp_all only
    apply distribLattice.sup_le

  inf H₁ H₂ := by
    cases H₁ with | mk H₁ H₁_prop
    cases H₂ with | mk H₂ H₂_prop
    constructor
    case val =>
      exact (min H₁ H₂)
    case property =>
      simp_all only [Set.mem_Iic]
      apply le_trans
      apply inf_le_left
      exact H₁_prop

  inf_le_left := by
    intros
    simp_all only
    apply distribLattice.inf_le_left

  inf_le_right := by
    intros
    simp_all only
    apply distribLattice.inf_le_right

  le_inf := by
    intros
    simp_all only
    apply distribLattice.le_inf
    all_goals
      simp only [Subtype.coe_le_coe]
      assumption
  top := ⟨G, by apply distribLattice.le_refl⟩
  le_top := by
    intro H
    cases H with | mk H Hprop
    simp at Hprop
    simp_all [Subtype.mk_le_mk]

  bot := ⟨Digraph.emptyDigraph V, by
        simp [Digraph.emptyDigraph,
          LE.le]⟩

  bot_le := by
    intro H
    cases H with | mk H Hprop
    simp at Hprop
    simp [Digraph.emptyDigraph, LE.le]

  compl H := by
    obtain ⟨H, Hprop⟩ := H
    constructor
    case val => exact {
      verts := G.verts
      -- The complement is defined w.r.t H.verts and G.Adj
      Adj v w := G.Adj v w ∧ ¬ H.Adj v w ∧ v ∈ G.verts ∧ w ∈ G.verts

    }
    case property =>
      simp at Hprop
      simp_all [LE.le]

  sSup ℋ := by
    constructor
    case val =>
      exact sSup {H | ∃p , ⟨H,p⟩ ∈ ℋ}
    case property =>
      simp_all [sSup]
      constructor
      · simp only [LE.le]
        rw [Set.subset_def]
        intro _ ⟨H, ⟨⟨⟨h, _⟩,_⟩, h'⟩⟩
        solve_by_elim
      · intro v w
        simp only [LE.le]
        intro ⟨H, ⟨⟨⟨_, h⟩, _⟩, _⟩⟩
        solve_by_elim

  le_sSup := by
    intro ℋ ⟨H, ⟨H_vert_prop, H_Adj_prop⟩⟩ hH
    simp_all only [LE.le, sSup, Set.mem_Iic, Set.subset_def, Set.mem_setOf_eq]
    constructor
    · intro v vHverts
      use H
      tauto
    · intro v w Hadj
      use H
      tauto

  sSup_le := by
    intro ℋ ⟨H, H_prop⟩ h
    simp_all only [LE.le, Subtype.forall, Set.mem_Iic, forall_and_index, sSup, Set.mem_setOf_eq,
      forall_exists_index, Set.subset_def]
    constructor
    · intro v H' H'_prop hadj h_mem
      simp at H_prop
      specialize h H' H'_prop hadj h_mem
      tauto
    · intro v w H' H'_prop hadj h_mem
      specialize h H' H'_prop hadj h_mem
      tauto

  top_le_sup_compl := by
    intro ⟨H, H_prop⟩
    simp_all only [LE.le, max, SemilatticeSup.sup, Set.subset_union_right, true_and]
    intro v w G_adj
    obtain ⟨H_verts, H_adj⟩ := H_prop
    by_cases hadj : H.Adj v w <;> simp_all
    · constructor
      · apply G.left_mem_verts_of_adj G_adj
      · apply G.right_mem_verts_of_adj G_adj

  sInf ℋ := by
    constructor
    case val =>
      exact sInf {H | ∃p , ⟨H,p⟩ ∈ ℋ}
    case property =>
      simp_all only [sInf, Set.mem_Iic, Set.mem_setOf_eq]
      constructor
      · simp [LE.le]
        rw [Set.subset_def]
        intro v hv
        simp at hv
        done
      · intro v w hadj
        simp at hadj
        done











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
