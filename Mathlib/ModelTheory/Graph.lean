/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.PartialEquiv
import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# First-Order Structures in Graph Theory

This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions

- `FirstOrder.Language.graph` is the language consisting of a single relation representing
  adjacency.
- `SimpleGraph.structure` is the first-order structure corresponding to a given simple graph.
- `FirstOrder.Language.Theory.simpleGraph` is the theory of simple graphs.
- `FirstOrder.Language.simpleGraphOfStructure` gives the simple graph corresponding to a model
  of the theory of simple graphs.
-/

universe u

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {V : Type u} {n : ℕ}

/-! ### Simple Graphs -/

/-- The type of relations for the language of graphs, consisting of a single binary relation `adj`.
-/
inductive graphRel : ℕ → Type
  | adj : graphRel 2
  deriving DecidableEq

/-- The language consisting of a single relation representing adjacency. -/
protected def graph : Language := ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational

/-- The symbol representing the adjacency relation. -/
abbrev adj : Language.graph.Relations 2 := .adj

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def _root_.SimpleGraph.structure (G : SimpleGraph V) : Language.graph.Structure V where
  RelMap | .adj => (fun x => G.Adj (x 0) (x 1))

namespace graph

instance instSubsingleton : Subsingleton (Language.graph.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

instance instIsEmptyRelZero : IsEmpty (Language.graph.Relations 0) :=
  ⟨by rintro ⟨⟩⟩

end graph

/-- The theory of simple graphs. -/
protected def Theory.simpleGraph : Language.graph.Theory :=
  {adj.irreflexive, adj.symmetric}

@[simp]
theorem Theory.simpleGraph_model_iff [Language.graph.Structure V] :
    V ⊨ Theory.simpleGraph ↔
      (Irreflexive fun x y : V => RelMap adj ![x, y]) ∧
        Symmetric fun x y : V => RelMap adj ![x, y] := by
  simp [Theory.simpleGraph]

instance simpleGraph_model (G : SimpleGraph V) :
    @Theory.Model _ V G.structure Theory.simpleGraph := by
  letI := G.structure
  rw [Theory.simpleGraph_model_iff]
  exact ⟨G.loopless, G.symm⟩

variable (V)

/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
def simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    SimpleGraph V where
  Adj x y := RelMap adj ![x, y]
  symm :=
    Relations.realize_symmetric.1
      (Theory.realize_sentence_of_mem Theory.simpleGraph
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  loopless :=
    Relations.realize_irreflexive.1
      (Theory.realize_sentence_of_mem Theory.simpleGraph (Set.mem_insert _ _))

variable {V}

@[simp]
theorem _root_.SimpleGraph.simpleGraphOfStructure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.structure _ = G := by
  ext
  rfl

@[simp]
theorem structure_simpleGraphOfStructure [S : Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    (simpleGraphOfStructure V).structure = S := by
  ext
  case funMap n f xs =>
    exact isEmptyElim f
  case RelMap n r xs =>
    match n, r with
    | 2, .adj =>
      rw [iff_eq_eq]
      change RelMap adj ![xs 0, xs 1] = _
      refine congr rfl (funext ?_)
      simp [Fin.forall_fin_two]

theorem Theory.simpleGraph_isSatisfiable : Theory.IsSatisfiable Theory.simpleGraph :=
  ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

namespace graph

variable (V) [S : Language.graph.Structure V]

@[simp]
theorem substructure_adj_iff {S : Language.graph.Substructure V} (x y : S) :
    RelMap adj ![x, y] ↔ RelMap adj ![(x : V), y] := by
  simp only [RelMap, Substructure.inducedStructure]
  constructor <;> intro h <;> convert h <;> rename_i n <;> match n with
    | 0 => rfl
    | 1 => rfl

variable [V ⊨ Theory.simpleGraph] {V}

theorem adj_irrefl : Irreflexive fun (x : V) y ↦ RelMap adj ![x, y] :=
  (Theory.simpleGraph_model_iff.1 (by assumption)).1

theorem adj_symm : Symmetric fun (x : V) y ↦ RelMap adj ![x, y] :=
  (Theory.simpleGraph_model_iff.1 (by assumption)).2

/-- Works better for rewrites.-/
theorem adj_symm' (x y : V) : RelMap adj ![x, y] ↔ RelMap adj ![y, x] :=
  ⟨adj_symm (x := x) (y := y), adj_symm (x := y) (y := x)⟩

theorem substructure_models_simpleGraph (S : Language.graph.Substructure V) :
    S ⊨ Theory.simpleGraph := by
  rw [Theory.simpleGraph_model_iff]
  simp_rw [substructure_adj_iff]
  exact ⟨fun x y ↦ adj_irrefl (V := V) x y, fun _ _ h ↦ adj_symm h⟩

instance (S : Language.graph.Substructure V) : S ⊨ Theory.simpleGraph :=
  substructure_models_simpleGraph S

variable [DecidableEq V] (V)

/-- A graph has the extension property if for for any two disjoint finite sets of vertices, there
  exists a vertex which is adjacent to all vertices in one and to no vertices in the other. It
  characterizes the Rado graph. -/
def ExtensionProperty : Prop :=
    ∀ {A B : Finset V}, ∀ (_ : Disjoint A B), ∃ v ∉ A ∪ B,
      (∀ a ∈ A, RelMap adj ![v, a]) ∧ ∀ b ∈ B, ¬ RelMap adj ![v, b]

variable {V} (W : Type*) [T : Language.graph.Structure W] [W ⊨ Theory.simpleGraph]

theorem ExtensionProperty.extensionPair_Countable (ext_prop : ExtensionProperty V) :
    IsExtensionPair Language.graph W V := by
  classical
  rename_i V_simple_graph _ W_simple_graph
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  let A := f '' {v | RelMap adj ![m, v]}
  have : Finite S := S_fg.finite
  let A_Finset := Set.Finite.toFinset (Finite.Set.finite_image .. : Finite A)
  let B := f '' {v | ¬ RelMap adj ![m, v]}
  let B_Finset := Set.Finite.toFinset (Finite.Set.finite_image .. : Finite B)
  have A_B_disjoint : Disjoint A_Finset B_Finset := by
    apply Set.Finite.disjoint_toFinset.2
    refine (Set.disjoint_image_iff f.injective).2 ?_
    rw [Set.disjoint_iff]
    intro _ hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    let ⟨_, _⟩ := hx
    contradiction
  have A_B_cover_image : ∀ x, f x ∈ A ∪ B := by
    intro x
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, A, B]
    exact Classical.em (RelMap adj ![m, ↑x])
  let ⟨v, v_not_in_AB, v_adj_A, v_not_adj_B⟩ := ext_prop A_B_disjoint
  simp only [A_Finset, B_Finset, Finset.mem_union, Set.Finite.mem_toFinset]
    at v_not_in_AB v_adj_A v_not_adj_B
  have v_not_in_image : ∀ x, f x ≠ v := fun x h ↦ v_not_in_AB (h ▸ A_B_cover_image x)
  have v_adj_iff_A : ∀ x : S, RelMap adj ![v, f x] ↔ f x ∈ A := by
    intro x
    refine ⟨?_, fun H ↦ v_adj_A (f x) H⟩
    intro v_adj_fx
    cases (Set.mem_union ..).1 (A_B_cover_image x)
    · assumption
    · by_contra
      exact v_not_adj_B (f x) (by assumption) (by assumption)
  cases Classical.em (m ∈ S)
  case inl m_in_S =>
    have : Substructure.closure _ {m} ⊔ S = S := by
      apply sup_eq_right.2
      exact Substructure.closure_le.2 (Set.singleton_subset_iff.2 m_in_S)
    use f.comp (Substructure.inclusion (le_of_eq this))
    rfl
  case inr m_not_in_S =>
    let S' := Substructure.closure Language.graph {m} ⊔ S
    have mem_S'_iff : ∀ x, x ∈ S' ↔ x = m ∨ x ∈ S := by
      intro x
      unfold S'
      rw [← Substructure.mem_coe, ← Substructure.closure_eq S, ← Substructure.closure_union]
      simp only [Set.singleton_union, Substructure.closure_eq_of_isRelational, Set.mem_insert_iff,
        SetLike.mem_coe, Substructure.closure_eq]
    let g (s : S') : V := if h : ↑s ∈ S then f ⟨s, h⟩ else v
    have g_morphism : ∀ x y, RelMap adj ![x, y] ↔ RelMap adj ![g x, g y] := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      unfold g
      cases (mem_S'_iff x).1 hx <;> cases (mem_S'_iff y).1 hy <;> rename_i h' h'' <;>
        simp only [h', h'', m_not_in_S, ↓reduceDIte, v_not_in_image, substructure_adj_iff]
      · constructor <;> intro H <;> by_contra <;> exact adj_irrefl _ H
      · rw [v_adj_iff_A]
        simp only [Set.mem_image, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
          A]
      · nth_rw 2 [adj_symm']
        rw [adj_symm', v_adj_iff_A]
        simp only [Set.mem_image, Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
          A]
      · have H := f.map_rel adj ![⟨x, h'⟩, ⟨y, h''⟩]
        rw [substructure_adj_iff] at H
        convert H.symm
        ext n
        match n with
        | 0 => rfl
        | 1 => rfl
    have g_inj : Function.Injective g := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ h
      simp only [Subtype.mk.injEq]
      unfold g at h
      cases (mem_S'_iff x).1 hx <;> cases (mem_S'_iff y).1 hy <;> rename_i h' h'' <;>
        simp only [h', h'', m_not_in_S, ↓reduceDIte, v_not_in_image] at h ⊢
      · by_contra
        exact v_not_in_image _ h.symm
      · convert f.injective h
        exact Subtype.mk_eq_mk.symm
    use {
      inj' := g_inj
      map_rel' := by
        intro n r
        cases r
        intro x
        have h := (g_morphism (x 0) (x 1)).symm
        have h' : ![g (x 0), g (x 1)] = g ∘ x := List.ofFn_inj.1 rfl
        have h'' : ![x 0, x 1] = x := List.ofFn_inj.1 rfl
        exact h' ▸ h'' ▸ h}
    ext x
    let ⟨x, x_in_S⟩ := x
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Set.inclusion_mk]
    change _ = Function.Embedding.toFun _ _
    simp only [x_in_S, ↓reduceDIte]

theorem ExtensionProperty.embedding_from_countable (ext_prop : ExtensionProperty V) [Countable W] :
    Nonempty (W ↪[Language.graph] V) :=
  ⟨Exists.choose <|
    embedding_from_cg (L := Language.graph) (M := W) (N := V) Structure.cg_of_countable
      inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations.default
        (ext_prop.extensionPair_Countable _)⟩

/-- Any graph satisfying the extension property is the Fraïssé limit of the class of finite
  graphs. -/
theorem ExtensionProperty.isFraisseLimit_finite_graphs (ext_prop : ExtensionProperty V)
    [Countable V] : IsFraisseLimit
      { G : CategoryTheory.Bundled Language.graph.Structure | G ⊨ Theory.simpleGraph ∧ Finite G }
        V := by
  constructor
  · rw [isUltrahomogeneous_iff_IsExtensionPair Structure.cg_of_countable]
    exact ext_prop.extensionPair_Countable V
  · ext G
    simp only [age, Set.mem_setOf_eq, Structure.fg_iff_finite]
    constructor
    · intro ⟨G_finite, ⟨f⟩⟩
      refine ⟨?_, G_finite⟩
      apply StrongHomClass.theory_model f.equivRange.symm
    · intro ⟨G_graph, G_finite⟩
      refine ⟨G_finite, ?_⟩
      apply ext_prop.embedding_from_countable (W := G)

end graph

end Language

end FirstOrder
