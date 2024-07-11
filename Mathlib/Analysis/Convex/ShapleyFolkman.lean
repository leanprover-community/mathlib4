/-
Copyright (c) 2024 Nick Decroos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Decroos.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Separation

namespace Convex

open Fintype Finset Set

universe u

-- Assume that we have a field 𝕜, a vector space E over 𝕜, and a finite index type
variable {𝕜 E ι : Type*} [Fintype ι] [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable {s : Set E} {x : E}{hx : x ∈ convexHull 𝕜 s}

/-!
# The Shapley-Folkman lemma

The Shapley-Folkman lemma states that

## Tags

convex hull, shapley-folkman

-/

/- **Shapley-Folkman's lemma** -/
/-
lemma shapley_folkman {N : ℕ}{Q : ι → Set E} {s : Finset ι}
  (x : E)
  (h_convex : ∀ i ∈ s, Convex 𝕜 (Q i))
  (h_finite : ∀ i ∈ s, Finite (Q i))
  (h_mem : x ∈ convexHull 𝕜 (∑ i in s, Q i)) :
  ∃ (q : ι → E), (∑ i in (finset.range N).to_finset, q i = x) ^
  ∀ i, q i ∈ convexHull 𝕜 (Q i) := sorry
-/

--   ((finset.range N).to_finset.filter (λ i, q i ∉ Q i)).card ≤ D ^

def finset_range_d_n (D N : ℕ) : Finset ℕ :=
(Finset.range (N + 1)).filter (λ n => D ≤ n)

theorem shapley_folkman{D N : ℕ}{Q : ι → Set E}
(hD : D ≤ Fintype.card ι)
(hN : N ≤ Fintype.card ι) :
convexHull 𝕜 (∑ n ∈ Finset.range N, Q n) ⊆ ⋃ (I : Finset ℕ) (hI: I.card = D), (∑ i ∈ I, convexHull 𝕜 (Q i)  + (∑ i ∈ finset_range_d_n D N, Q i) )  := sorry

-- + (∑ i ∈ range I, Q i)
end Convex
