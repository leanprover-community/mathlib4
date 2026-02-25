/-
Copyright (c) 2026 Iván Renison, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Kyle Miller
-/
module

public import Mathlib.Combinatorics.HasAdj.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

@[expose] public section

namespace HasAdj

variable {α : Type*} {Gr : Type*} [HasAdj α Gr]

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure Dart (G : Gr) extends α × α where
  adj : Adj G fst snd

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G : Gr}

theorem Dart.ext_iff (d₁ d₂ : Dart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp

@[ext]
theorem Dart.ext (d₁ d₂ : Dart G) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h

theorem Dart.toProd_injective : Function.Injective (Dart.toProd : Dart G → α × α) :=
  Dart.ext

instance [DecidableEq α] (G : Gr) : DecidableEq (Dart G) :=
  Dart.toProd_injective.decidableEq

instance Dart.fintype [Fintype α] [DecidableRel (Adj G)] : Fintype (Dart G) :=
  Fintype.ofEquiv (Σ v, { w | Adj G v w })
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : Dart G) : Prop :=
  d.snd = d'.fst

end HasAdj
