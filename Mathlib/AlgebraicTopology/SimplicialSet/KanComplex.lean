/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Kan complexes

In this file we give the definition of Kan complexes.
In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.
- Generalize the definition to higher universes.
  Since `Λ[n, i]` is an object of `SSet.{0}`,
  the current definition of a Kan complex `S`
  requires `S : SSet.{0}`.

-/

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *Kan complex* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
class KanComplex (S : SSet) : Prop where
  hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ

end SSet
