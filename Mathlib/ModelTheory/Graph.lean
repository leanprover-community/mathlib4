/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Combinatorics.SimpleGraph.Basic

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



universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {L : Language.{u, v}} {α : Type w} {V : Type w'} {n : ℕ}

/-! ### Simple Graphs -/


/-- The language consisting of a single relation representing adjacency. -/
protected def graph : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit

/-- The symbol representing the adjacency relation. -/
def adj : Language.graph.Relations 2 :=
  Unit.unit

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def _root_.SimpleGraph.structure (G : SimpleGraph V) : Language.graph.Structure V :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => G.Adj

namespace graph

instance instIsRelational : IsRelational Language.graph :=
  Language.isRelational_mk₂

instance instSubsingleton : Subsingleton (Language.graph.Relations n) :=
  Language.subsingleton_mk₂_relations

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
  simp only [@Theory.simpleGraph_model_iff _ G.structure, relMap_apply₂]
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
    exact (IsRelational.empty_functions n).elim f
  case RelMap n r xs =>
    rw [iff_eq_eq]
    cases' n with n
    · exact r.elim
    · cases' n with n
      · exact r.elim
      · cases' n with n
        · cases r
          change RelMap adj ![xs 0, xs 1] = _
          refine congr rfl (funext ?_)
          simp [Fin.forall_fin_two]
        · exact r.elim

theorem Theory.simpleGraph_isSatisfiable : Theory.IsSatisfiable Theory.simpleGraph :=
  ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

end Language

end FirstOrder
