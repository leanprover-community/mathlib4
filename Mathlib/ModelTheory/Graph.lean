/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.graph
! leanprover-community/mathlib commit e56b8fea84d60fe434632b9d3b829ee685fb0c8f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Satisfiability
import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# First-Ordered Structures in Graph Theory
This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions
* `first_order.language.graph` is the language consisting of a single relation representing
adjacency.
* `simple_graph.Structure` is the first-order structure corresponding to a given simple graph.
* `first_order.language.Theory.simple_graph` is the theory of simple graphs.
* `first_order.language.simple_graph_of_structure` gives the simple graph corresponding to a model
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
#align first_order.language.graph FirstOrder.Language.graph

/-- The symbol representing the adjacency relation. -/
def adj : Language.graph.Relations 2 :=
  Unit.unit
#align first_order.language.adj FirstOrder.Language.adj

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def SimpleGraph.structure (G : SimpleGraph V) : Language.graph.Structure V :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => G.Adj
#align simple_graph.Structure SimpleGraph.structure

namespace Graph

instance : IsRelational Language.graph :=
  Language.isRelational_mk₂

instance : Subsingleton (Language.graph.Relations n) :=
  Language.subsingleton_mk₂_relations

end Graph

/-- The theory of simple graphs. -/
protected def Theory.simpleGraph : Language.graph.Theory :=
  {adj.Irreflexive, adj.Symmetric}
#align first_order.language.Theory.simple_graph FirstOrder.Language.Theory.simpleGraph

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Theory.simpleGraph_model_iff [Language.graph.Structure V] :
    V ⊨ Theory.simpleGraph ↔
      (Irreflexive fun x y : V => RelMap adj ![x, y]) ∧
        Symmetric fun x y : V => RelMap adj ![x, y] :=
  by simp [Theory.simple_graph]
#align first_order.language.Theory.simple_graph_model_iff FirstOrder.Language.Theory.simpleGraph_model_iff

instance simpleGraph_model (G : SimpleGraph V) : @Theory.Model _ V G.Structure Theory.simpleGraph :=
  by
  simp only [Theory.simple_graph_model_iff, rel_map_apply₂]
  exact ⟨G.loopless, G.symm⟩
#align first_order.language.simple_graph_model FirstOrder.Language.simpleGraph_model

variable (V)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
def simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simpleGraph] : SimpleGraph V
    where
  Adj x y := RelMap adj ![x, y]
  symm :=
    Relations.realize_symmetric.1
      (Theory.realize_sentence_of_mem Theory.simpleGraph
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  loopless :=
    Relations.realize_irreflexive.1
      (Theory.realize_sentence_of_mem Theory.simpleGraph (Set.mem_insert _ _))
#align first_order.language.simple_graph_of_structure FirstOrder.Language.simpleGraphOfStructure

variable {V}

@[simp]
theorem SimpleGraph.simpleGraphOfStructure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.Structure _ = G :=
  by
  ext
  rfl
#align simple_graph.simple_graph_of_structure SimpleGraph.simpleGraphOfStructure

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem structure_simpleGraphOfStructure [S : Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    (simpleGraphOfStructure V).Structure = S :=
  by
  ext (n f xs)
  · exact (is_relational.empty_functions n).elim f
  · ext (n r xs)
    rw [iff_eq_eq]
    cases n
    · exact r.elim
    · cases n
      · exact r.elim
      · cases n
        · cases r
          change rel_map adj ![xs 0, xs 1] = _
          refine' congr rfl (funext _)
          simp [Fin.forall_fin_two]
        · exact r.elim
#align first_order.language.Structure_simple_graph_of_structure FirstOrder.Language.structure_simpleGraphOfStructure

theorem Theory.simpleGraph_isSatisfiable : Theory.IsSatisfiable Theory.simpleGraph :=
  ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩
#align first_order.language.Theory.simple_graph_is_satisfiable FirstOrder.Language.Theory.simpleGraph_isSatisfiable

end Language

end FirstOrder

