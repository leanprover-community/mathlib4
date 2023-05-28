/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.Graph.Hom
import Mathlib.Data.Set.Finite

/-! # Darts

This module defines the `Graph.Dart G` type of darts for graphs that have
a `HasAdj` instance.

## Main definitions

* `Graph.Dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

-/

namespace Graph
variable {Γ Γ' : Type _} {V : Γ → Type u} {V' : Γ' → Type u'}
variable [HasAdj Γ V] [HasAdj Γ' V']

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart (G : Γ) extends (V G) × (V G) where
  is_adj : Adj G fst snd
#align simple_graph.dart Graph.Dart

initialize_simps_projections Dart (+toProd, -fst, -snd)

pp_extended_field_notation Dart

variable {G : Γ}

theorem Dart.ext_iff (d₁ d₂ : Dart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp
#align simple_graph.dart.ext_iff Graph.Dart.ext_iff

@[ext]
theorem Dart.ext (d₁ d₂ : Dart G) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h
#align simple_graph.dart.ext Graph.Dart.ext

instance [DecidableEq (V G)] : DecidableEq (Dart G)
  | d₁, d₂ =>
    if h : d₁.toProd = d₂.toProd then
      isTrue (Dart.ext _ _ h)
    else
      isFalse (by rintro rfl; exact (h rfl).elim)

-- Porting note: deleted `Dart.fst` and `Dart.snd` since they are now invalid declaration names,
-- even though there is not actually a `SimpleGraph.Dart.fst` or `SimpleGraph.Dart.snd`.

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : Dart G → V G × V G) := Dart.ext
#align simple_graph.dart.to_prod_injective Graph.Dart.toProd_injective

instance Dart.fintype [Fintype (V G)] [DecidableRel (Adj G)] : Fintype (Dart G) :=
  Fintype.ofEquiv (Σ v, {w | Adj G v w})
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩
      left_inv := fun s => by ext <;> simp
      right_inv := fun d => by ext <;> simp }
#align simple_graph.dart.fintype Graph.Dart.fintype

namespace Hom
variable {G : Γ} {G' : Γ'} (f : G →g G')

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : Dart G) : Dart G' := ⟨d.1.map f f, f.map_adj d.2⟩
#align simple_graph.hom.map_dart Graph.Hom.mapDart

@[simp]
theorem mapDart_apply (d : Dart G) : mapDart f d = ⟨d.1.map f f, f.map_adj d.2⟩ := rfl
#align simple_graph.hom.map_dart_apply Graph.Hom.mapDart_apply

end Hom

end Graph
