/-
Copyright (c) 2025 Evan Spotte-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Hypergraph.Basic

open Finset Hypergraph

variable {α β : Type*} {x y z : α} {s t : Set α} {e f g : β} {l m : Set β} [Fintype α] [Fintype β]
variable {H₁ : Hypergraph γ δ} [Fintype H₁.vertexSet] [Fintype H₁.hyperedgeSet]

-- TODO: rank and co-rank
-- Requires us to know the sizes of every hyperedge
-- Problem: hyperedges can be non-finite
-- Second problem: hyperedge sizes (I think) need to be in a list

-- noncomputable def rank (H₁ : Hypergraph γ δ) : ENat :=
--   List.maximum (Finset.toList (Set.toFinset { Set.ncard s | s ∈ H₁.hyperedgeVertexSet}))
