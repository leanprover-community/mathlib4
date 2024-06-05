/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq
#align simple_graph.dart SimpleGraph.Dart

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G}

theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp
#align simple_graph.dart.ext_iff SimpleGraph.Dart.ext_iff

@[ext]
theorem Dart.ext (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h
#align simple_graph.dart.ext SimpleGraph.Dart.ext

-- Porting note: deleted `Dart.fst` and `Dart.snd` since they are now invalid declaration names,
-- even though there is not actually a `SimpleGraph.Dart.fst` or `SimpleGraph.Dart.snd`.

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  Dart.ext
#align simple_graph.dart.to_prod_injective SimpleGraph.Dart.toProd_injective

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩
      left_inv := fun s => by ext <;> simp
      right_inv := fun d => by ext <;> simp }
#align simple_graph.dart.fintype SimpleGraph.Dart.fintype

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  Sym2.mk d.toProd
#align simple_graph.dart.edge SimpleGraph.Dart.edge

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = Sym2.mk p :=
  rfl
#align simple_graph.dart.edge_mk SimpleGraph.Dart.edge_mk

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.edgeSet :=
  d.adj
#align simple_graph.dart.edge_mem SimpleGraph.Dart.edge_mem

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, G.symm d.adj⟩
#align simple_graph.dart.symm SimpleGraph.Dart.symm

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl
#align simple_graph.dart.symm_mk SimpleGraph.Dart.symm_mk

@[simp]
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.mk_prod_swap_eq
#align simple_graph.dart.edge_symm SimpleGraph.Dart.edge_symm

@[simp]
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm
#align simple_graph.dart.edge_comp_symm SimpleGraph.Dart.edge_comp_symm

@[simp]
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _
#align simple_graph.dart.symm_symm SimpleGraph.Dart.symm_symm

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  Dart.symm_symm
#align simple_graph.dart.symm_involutive SimpleGraph.Dart.symm_involutive

theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne
#align simple_graph.dart.symm_ne SimpleGraph.Dart.symm_ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp
#align simple_graph.dart_edge_eq_iff SimpleGraph.dart_edge_eq_iff

theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {p : V × V}, d.edge = Sym2.mk p ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  apply Sym2.mk_eq_mk_iff
#align simple_graph.dart_edge_eq_mk_iff SimpleGraph.dart_edge_eq_mk'_iff

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp
#align simple_graph.dart_edge_eq_mk_iff' SimpleGraph.dart_edge_eq_mk'_iff'

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst
#align simple_graph.dart_adj SimpleGraph.DartAdj

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩
#align simple_graph.dart_of_neighbor_set SimpleGraph.dartOfNeighborSet

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'
#align simple_graph.dart_of_neighbor_set_injective SimpleGraph.dartOfNeighborSet_injective

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩
#align simple_graph.nonempty_dart_top SimpleGraph.nonempty_dart_top

end SimpleGraph
