/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.HasAdj.Dart
public import Mathlib.Combinatorics.SimpleGraph.HasAdj

/-!
# Darts in simple graphs

This files gives simple-graph-specific properties of darts.
-/

@[expose] public section

namespace HasAdj

variable {V : Type*} {G : SimpleGraph V}

/-- The edge associated to the dart. -/
def Dart.edge (d : Dart G) : Sym2 V := s(d.fst, d.snd)

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = s(p.1, p.2) :=
  rfl

@[simp]
theorem Dart.edge_mem (d : Dart G) : d.edge ∈ G.edgeSet :=
  d.adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : Dart G) : Dart G :=
  ⟨d.toProd.swap, G.symm d.adj⟩

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
theorem Dart.edge_symm (d : Dart G) : d.symm.edge = d.edge :=
  Sym2.eq_swap

@[simp]
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : Dart G → Sym2 V) :=
  funext Dart.edge_symm

@[simp]
theorem Dart.symm_symm (d : Dart G) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : Dart G → Dart G) :=
  Dart.symm_symm

theorem Dart.symm_ne (d : Dart G) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : Dart G, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp

theorem dart_edge_eq_mk'_iff :
    ∀ {d : Dart G} {u v : V}, d.edge = s(u, v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u) := by
  rintro ⟨p, h⟩ _ _
  simp

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : Dart G} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : Dart G :=
  ⟨(v, w), w.property⟩

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (dartOfNeighborSet G v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

instance nonempty_dart_top [Nontrivial V] : Nonempty (Dart (⊤ : SimpleGraph V)) := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end HasAdj
