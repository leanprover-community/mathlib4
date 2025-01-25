/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Kan complexes

In this file we give the definition of Kan complexes.
In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

universe u

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *Kan complex* if it satisfies the following horn-filling condition:
for every nonzero `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
class KanComplex (S : SSet.{u}) : Prop where
  hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 2)⦄ (σ₀ : Λ[n + 1, i] ⟶ S),
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = hornInclusion (n + 1) i ≫ σ

end SSet
