/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Antichain

#align_import combinatorics.simple_graph.coloring from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper
colorings in the literature). A graph coloring is the attribution of
"colors" to all of its vertices such that adjacent vertices have
different colors. A coloring can be represented as a homomorphism into
a complete graph, whose vertices represent the colors.

## Main definitions

* `G.Coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.Colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromaticNumber` is the minimal `n` such that `G` is
  `n`-colorable, or `0` if it cannot be colored with finitely many
  colors.

* `C.colorClass c` is the set of vertices colored by `c : α` in the
  coloring `C : G.Coloring α`.

* `C.colorClasses` is the set containing all color classes.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)
-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g (⊤ : SimpleGraph α)
#align simple_graph.coloring SimpleGraph.Coloring

variable {G} {α : Type v} (C : G.Coloring α)

theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h
#align simple_graph.coloring.valid SimpleGraph.Coloring.valid

/-- Construct a term of `SimpleGraph.Coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `SimpleGraph.Hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[match_pattern]
def Coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) :
    G.Coloring α :=
  ⟨color, @valid⟩
#align simple_graph.coloring.mk SimpleGraph.Coloring.mk

/-- The color class of a given color.
-/
def Coloring.colorClass (c : α) : Set V := { v : V | C v = c }
#align simple_graph.coloring.color_class SimpleGraph.Coloring.colorClass

/-- The set containing all color classes. -/
def Coloring.colorClasses : Set (Set V) := (Setoid.ker C).classes
#align simple_graph.coloring.color_classes SimpleGraph.Coloring.colorClasses

theorem Coloring.mem_colorClass (v : V) : v ∈ C.colorClass (C v) := rfl
#align simple_graph.coloring.mem_color_class SimpleGraph.Coloring.mem_colorClass

theorem Coloring.colorClasses_isPartition : Setoid.IsPartition C.colorClasses :=
  Setoid.isPartition_classes (Setoid.ker C)
#align simple_graph.coloring.color_classes_is_partition SimpleGraph.Coloring.colorClasses_isPartition

theorem Coloring.mem_colorClasses {v : V} : C.colorClass (C v) ∈ C.colorClasses :=
  ⟨v, rfl⟩
#align simple_graph.coloring.mem_color_classes SimpleGraph.Coloring.mem_colorClasses

theorem Coloring.colorClasses_finite [Finite α] : C.colorClasses.Finite :=
  Setoid.finite_classes_ker _
#align simple_graph.coloring.color_classes_finite SimpleGraph.Coloring.colorClasses_finite

theorem Coloring.card_colorClasses_le [Fintype α] [Fintype C.colorClasses] :
    Fintype.card C.colorClasses ≤ Fintype.card α := by
  simp [colorClasses]
  -- porting note: brute force instance declaration `[Fintype (Setoid.classes (Setoid.ker C))]`
  haveI : Fintype (Setoid.classes (Setoid.ker C)) := by assumption
  convert Setoid.card_classes_ker_le C
#align simple_graph.coloring.card_color_classes_le SimpleGraph.Coloring.card_colorClasses_le

theorem Coloring.not_adj_of_mem_colorClass {c : α} {v w : V} (hv : v ∈ C.colorClass c)
    (hw : w ∈ C.colorClass c) : ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))
#align simple_graph.coloring.not_adj_of_mem_color_class SimpleGraph.Coloring.not_adj_of_mem_colorClass

theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.colorClass c) :=
  fun _ hv _ hw _ => C.not_adj_of_mem_colorClass hv hw
#align simple_graph.coloring.color_classes_independent SimpleGraph.Coloring.color_classes_independent

-- TODO make this computable
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
  change Fintype (RelHom G.Adj (⊤ : SimpleGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective

variable (G)

/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))
#align simple_graph.colorable SimpleGraph.Colorable

/-- The coloring of an empty graph. -/
def coloringOfIsEmpty [IsEmpty V] : G.Coloring α :=
  Coloring.mk isEmptyElim fun {v} => isEmptyElim v
#align simple_graph.coloring_of_is_empty SimpleGraph.coloringOfIsEmpty

theorem colorable_of_isEmpty [IsEmpty V] (n : ℕ) : G.Colorable n :=
  ⟨G.coloringOfIsEmpty⟩
#align simple_graph.colorable_of_is_empty SimpleGraph.colorable_of_isEmpty

theorem isEmpty_of_colorable_zero (h : G.Colorable 0) : IsEmpty V := by
  constructor
  intro v
  obtain ⟨i, hi⟩ := h.some v
  exact Nat.not_lt_zero _ hi
#align simple_graph.is_empty_of_colorable_zero SimpleGraph.isEmpty_of_colorable_zero

/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def selfColoring : G.Coloring V := Coloring.mk id fun {_ _} => G.ne_of_adj
#align simple_graph.self_coloring SimpleGraph.selfColoring

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromaticNumber : ℕ :=
  sInf { n : ℕ | G.Colorable n }
#align simple_graph.chromatic_number SimpleGraph.chromaticNumber

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolorOfEmbedding {α β : Type*} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β where
  toFun C := (Embedding.completeGraph f).toHom.comp C
  inj' := by -- this was strangely painful; seems like missing lemmas about embeddings
    intro C C' h
    dsimp only at h
    ext v
    apply (Embedding.completeGraph f).inj'
    change ((Embedding.completeGraph f).toHom.comp C) v = _
    rw [h]
    rfl
#align simple_graph.recolor_of_embedding SimpleGraph.recolorOfEmbedding

/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolorOfEquiv {α β : Type*} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply
#align simple_graph.recolor_of_equiv SimpleGraph.recolorOfEquiv

/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β]
    (hn : Fintype.card α ≤ Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding <| (Function.Embedding.nonempty_of_card_le hn).some
#align simple_graph.recolor_of_card_le SimpleGraph.recolorOfCardLE

variable {G}

theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩
#align simple_graph.colorable.mono SimpleGraph.Colorable.mono

theorem Coloring.to_colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLE (by simp) C⟩
#align simple_graph.coloring.to_colorable SimpleGraph.Coloring.to_colorable

theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.to_colorable
#align simple_graph.colorable_of_fintype SimpleGraph.colorable_of_fintype

/-- Noncomputably get a coloring from colorability. -/
noncomputable def Colorable.toColoring [Fintype α] {n : ℕ} (hc : G.Colorable n)
    (hn : n ≤ Fintype.card α) : G.Coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some
#align simple_graph.colorable.to_coloring SimpleGraph.Colorable.toColoring

theorem Colorable.of_embedding {V' : Type*} {G' : SimpleGraph V'} (f : G ↪g G') {n : ℕ}
    (h : G'.Colorable n) : G.Colorable n :=
  ⟨(h.toColoring (by simp)).comp f⟩
#align simple_graph.colorable.of_embedding SimpleGraph.Colorable.of_embedding

theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
    G.Colorable n ↔ ∃ C : G.Coloring ℕ, ∀ v, C v < n := by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    cases' C with color valid
    exact Fin.is_lt (color v)
  · rintro ⟨C, Cf⟩
    refine' ⟨Coloring.mk _ _⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne.def]
      exact C.valid hvw
#align simple_graph.colorable_iff_exists_bdd_nat_coloring SimpleGraph.colorable_iff_exists_bdd_nat_coloring

theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.Colorable n) :
    { n : ℕ | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩
#align simple_graph.colorable_set_nonempty_of_colorable SimpleGraph.colorable_set_nonempty_of_colorable

theorem chromaticNumber_bddBelow : BddBelow { n : ℕ | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le _⟩
#align simple_graph.chromatic_number_bdd_below SimpleGraph.chromaticNumber_bddBelow

theorem chromaticNumber_le_of_colorable {n : ℕ} (hc : G.Colorable n) : G.chromaticNumber ≤ n := by
  rw [chromaticNumber]
  apply csInf_le chromaticNumber_bddBelow
  constructor
  exact Classical.choice hc
#align simple_graph.chromatic_number_le_of_colorable SimpleGraph.chromaticNumber_le_of_colorable

theorem chromaticNumber_le_card [Fintype α] (C : G.Coloring α) :
    G.chromaticNumber ≤ Fintype.card α :=
  csInf_le chromaticNumber_bddBelow C.to_colorable
#align simple_graph.chromatic_number_le_card SimpleGraph.chromaticNumber_le_card

theorem colorable_chromaticNumber {m : ℕ} (hc : G.Colorable m) : G.Colorable G.chromaticNumber := by
  classical
  dsimp only [chromaticNumber]
  rw [Nat.sInf_def]
  apply Nat.find_spec
  exact colorable_set_nonempty_of_colorable hc
#align simple_graph.colorable_chromatic_number SimpleGraph.colorable_chromaticNumber

theorem colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] :
    G.Colorable G.chromaticNumber := by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype
#align simple_graph.colorable_chromatic_number_of_fintype SimpleGraph.colorable_chromaticNumber_of_fintype

theorem chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] :
    G.chromaticNumber ≤ 1 := by
  rw [chromaticNumber]
  apply csInf_le chromaticNumber_bddBelow
  constructor
  refine' Coloring.mk (fun _ => 0) _
  intro v w
  rw [Subsingleton.elim v w]
  simp
#align simple_graph.chromatic_number_le_one_of_subsingleton SimpleGraph.chromaticNumber_le_one_of_subsingleton

theorem chromaticNumber_eq_zero_of_isempty (G : SimpleGraph V) [IsEmpty V] :
    G.chromaticNumber = 0 := by
  rw [← nonpos_iff_eq_zero]
  apply csInf_le chromaticNumber_bddBelow
  apply colorable_of_isEmpty
#align simple_graph.chromatic_number_eq_zero_of_isempty SimpleGraph.chromaticNumber_eq_zero_of_isempty

theorem isEmpty_of_chromaticNumber_eq_zero (G : SimpleGraph V) [Finite V]
    (h : G.chromaticNumber = 0) : IsEmpty V := by
  have h' := G.colorable_chromaticNumber_of_fintype
  rw [h] at h'
  exact G.isEmpty_of_colorable_zero h'
#align simple_graph.is_empty_of_chromatic_number_eq_zero SimpleGraph.isEmpty_of_chromaticNumber_eq_zero

theorem chromaticNumber_pos [Nonempty V] {n : ℕ} (hc : G.Colorable n) : 0 < G.chromaticNumber := by
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁: i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁
#align simple_graph.chromatic_number_pos SimpleGraph.chromaticNumber_pos

theorem colorable_of_chromaticNumber_pos (h : 0 < G.chromaticNumber) :
    G.Colorable G.chromaticNumber := by
  obtain ⟨h, hn⟩ := Nat.nonempty_of_pos_sInf h
  exact colorable_chromaticNumber hn
#align simple_graph.colorable_of_chromatic_number_pos SimpleGraph.colorable_of_chromaticNumber_pos

theorem Colorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ} (hc : G'.Colorable n) :
    G.Colorable n :=
  ⟨hc.some.comp (Hom.mapSpanningSubgraphs h)⟩
#align simple_graph.colorable.mono_left SimpleGraph.Colorable.mono_left

theorem Colorable.chromaticNumber_le_of_forall_imp {V' : Type*} {G' : SimpleGraph V'} {m : ℕ}
    (hc : G'.Colorable m) (h : ∀ n, G'.Colorable n → G.Colorable n) :
    G.chromaticNumber ≤ G'.chromaticNumber := by
  apply csInf_le chromaticNumber_bddBelow
  apply h
  apply colorable_chromaticNumber hc
#align simple_graph.colorable.chromatic_number_le_of_forall_imp SimpleGraph.Colorable.chromaticNumber_le_of_forall_imp

theorem Colorable.chromaticNumber_mono (G' : SimpleGraph V) {m : ℕ} (hc : G'.Colorable m)
    (h : G ≤ G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  hc.chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h
#align simple_graph.colorable.chromatic_number_mono SimpleGraph.Colorable.chromaticNumber_mono

theorem Colorable.chromaticNumber_mono_of_embedding {V' : Type*} {G' : SimpleGraph V'} {n : ℕ}
    (h : G'.Colorable n) (f : G ↪g G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  h.chromaticNumber_le_of_forall_imp fun _ => Colorable.of_embedding f
#align simple_graph.colorable.chromatic_number_mono_of_embedding SimpleGraph.Colorable.chromaticNumber_mono_of_embedding

theorem chromaticNumber_eq_card_of_forall_surj [Fintype α] (C : G.Coloring α)
    (h : ∀ C' : G.Coloring α, Function.Surjective C') : G.chromaticNumber = Fintype.card α := by
  apply le_antisymm
  · apply chromaticNumber_le_card C
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨n, cn, hc⟩ :=
      exists_lt_of_csInf_lt (colorable_set_nonempty_of_colorable C.to_colorable) hc
    rw [← Fintype.card_fin n] at hc
    have f := (Function.Embedding.nonempty_of_card_le (le_of_lt hc)).some
    have C' := cn.some
    specialize h (G.recolorOfEmbedding f C')
    have h1 : Function.Surjective f := Function.Surjective.of_comp h
    have h2 := Fintype.card_le_of_surjective _ h1
    exact Nat.lt_le_asymm hc h2
#align simple_graph.chromatic_number_eq_card_of_forall_surj SimpleGraph.chromaticNumber_eq_card_of_forall_surj

theorem chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 := by
  let C : (⊥ : SimpleGraph V).Coloring (Fin 1) :=
      Coloring.mk (fun _ => 0) fun {v w} h => False.elim h
  apply le_antisymm
  · exact chromaticNumber_le_card C
  · exact chromaticNumber_pos C.to_colorable
#align simple_graph.chromatic_number_bot SimpleGraph.chromaticNumber_bot

@[simp]
theorem chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  apply chromaticNumber_eq_card_of_forall_surj (selfColoring _)
  intro C
  rw [← Finite.injective_iff_surjective]
  intro v w
  contrapose
  intro h
  exact C.valid h
#align simple_graph.chromatic_number_top SimpleGraph.chromaticNumber_top

theorem chromaticNumber_top_eq_zero_of_infinite (V : Type*) [Infinite V] :
    (⊤ : SimpleGraph V).chromaticNumber = 0 := by
  let n := (⊤ : SimpleGraph V).chromaticNumber
  by_contra hc
  replace hc := pos_iff_ne_zero.mpr hc
  apply Nat.not_succ_le_self n
  convert_to (⊤ : SimpleGraph { m | m < n + 1 }).chromaticNumber ≤ _
  · rw [SimpleGraph.chromaticNumber_top, Fintype.card_ofFinset,
        Finset.card_range, Nat.succ_eq_add_one]
  refine' (colorable_of_chromaticNumber_pos hc).chromaticNumber_mono_of_embedding _
  apply Embedding.completeGraph
  exact (Function.Embedding.subtype _).trans (Infinite.natEmbedding V)
#align simple_graph.chromatic_number_top_eq_zero_of_infinite SimpleGraph.chromaticNumber_top_eq_zero_of_infinite

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def CompleteBipartiteGraph.bicoloring (V W : Type*) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)
#align simple_graph.complete_bipartite_graph.bicoloring SimpleGraph.CompleteBipartiteGraph.bicoloring

theorem CompleteBipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  apply chromaticNumber_eq_card_of_forall_surj (CompleteBipartiteGraph.bicoloring V W)
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  have hn := C.valid h
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  · by_cases he' : C (Sum.inr w) = b
    · exact ⟨_, he'⟩
    · exfalso
      cases b <;>
        simp only [Bool.eq_true_eq_not_eq_false, Bool.eq_false_eq_not_eq_true] at he he' <;>
          rw [he, he'] at hn <;>
        contradiction
#align simple_graph.complete_bipartite_graph.chromatic_number SimpleGraph.CompleteBipartiteGraph.chromaticNumber

/-! ### Cliques -/


theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α]
    (C : G.Coloring α) : s.card ≤ Fintype.card α := by
  rw [isClique_iff_induce_eq] at h
  have f : G.induce ↑s ↪g G := Embedding.comap (Function.Embedding.subtype fun x => x ∈ ↑s) G
  rw [h] at f
  convert Fintype.card_le_of_injective _ (C.comp f.toHom).injective_of_top_hom using 1
  simp
#align simple_graph.is_clique.card_le_of_coloring SimpleGraph.IsClique.card_le_of_coloring

theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) {n : ℕ}
    (hc : G.Colorable n) : s.card ≤ n := by
  convert h.card_le_of_coloring hc.some
  simp
#align simple_graph.is_clique.card_le_of_colorable SimpleGraph.IsClique.card_le_of_colorable

-- TODO eliminate `Finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem IsClique.card_le_chromaticNumber [Finite V] {s : Finset V} (h : G.IsClique s) :
    s.card ≤ G.chromaticNumber := by
  cases nonempty_fintype V
  exact h.card_le_of_colorable G.colorable_chromaticNumber_of_fintype
#align simple_graph.is_clique.card_le_chromatic_number SimpleGraph.IsClique.card_le_chromaticNumber

protected theorem Colorable.cliqueFree {n m : ℕ} (hc : G.Colorable n) (hm : n < m) :
    G.CliqueFree m := by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)
#align simple_graph.colorable.clique_free SimpleGraph.Colorable.cliqueFree

-- TODO eliminate `Finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem cliqueFree_of_chromaticNumber_lt [Finite V] {n : ℕ} (hc : G.chromaticNumber < n) :
    G.CliqueFree n :=
  G.colorable_chromaticNumber_of_fintype.cliqueFree hc
#align simple_graph.clique_free_of_chromatic_number_lt SimpleGraph.cliqueFree_of_chromaticNumber_lt

end SimpleGraph
