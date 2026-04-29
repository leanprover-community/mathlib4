/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.GraphLike
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

@[expose] public section

open HasSourceTarget HasEdge HasInvol SymmDartLike SymmGraphLike GraphLike

variable {V : Type*} {G : SimpleGraph V} {d : V × V}

namespace GraphLike

theorem fst_ne_snd_of_mem_darts (hd : d ∈ darts G) : d.fst ≠ d.snd :=
  fun h ↦ G.irrefl <| h ▸ (show G.Adj d.1 d.2 from adj_of_mem_darts hd)

theorem snd_ne_fst_of_mem_darts (hd : d ∈ darts G) : d.snd ≠ d.fst :=
  fun h ↦ G.irrefl <| h ▸ (show G.Adj d.1 d.2 from adj_of_mem_darts hd)

theorem step.ne {u v} (s : step G u v) : u ≠ v := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  exact fst_ne_snd_of_mem_darts hd

instance {u} : IsEmpty (step G u u) where
  false s := step.ne s rfl

@[simp]
theorem dartSym2_mem (d : darts G) : dartSym2 d ∈ G.edgeSet :=
  d.prop

theorem dartSymm_ne (d : darts G) : dartSymm d ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Subtype.val) d.prop.ne

end GraphLike

namespace SimpleGraph

variable (G)

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : darts G :=
  ⟨(v, w), w.property⟩

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h => Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

lemma nonempty_darts_top [Nontrivial V] : (darts (⊤ : SimpleGraph V)).Nonempty := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨(v, w), h⟩

end SimpleGraph
