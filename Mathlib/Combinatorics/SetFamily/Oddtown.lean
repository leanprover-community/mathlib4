/-
Copyright (c) 2026 Justin Halford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Halford
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# The linear algebra method for set families: Oddtown

This file develops the basic form of the *linear algebra method* in extremal combinatorics
(Babai–Frankl) and gives its standard first application, the **Oddtown theorem**.

The method sends a finset to its characteristic vector over a field, arranges for the
hypotheses of the combinatorial problem to force the Gram matrix of those vectors to be the
identity, and concludes that the family is no larger than the dimension of the ambient space.

## Main definitions

* `Finset.charVec`: the characteristic vector of a finset, valued in a semiring.

## Main results

* `linearIndependent_of_dotProduct_eq_ite`: a family of vectors whose pairwise dot products
  form the identity matrix is linearly independent. This is the engine of the method.
* `Finset.charVec_dotProduct_charVec`: the dot product of two characteristic vectors is the
  cardinality of the intersection.
* `Finset.card_le_card_of_odd_card_of_even_card_inter`: the **Oddtown theorem**. A family of
  finsets of odd cardinality, any two of which meet in an even number of elements, has at most
  `Fintype.card α` members.

## References

* L. Babai and P. Frankl, *Linear Algebra Methods in Combinatorics*,
  Department of Computer Science, University of Chicago, 1992.
* E. R. Berlekamp, *On subsets with intersections of even cardinality*,
  Canad. Math. Bull. 12 (1969), 471–474.

## Implementation notes

This file was written with AI assistance (Claude Opus 5), then checked against the Lean kernel;
`#print axioms` on each result reports only `propext`, `Classical.choice`, `Quot.sound`.

## Tags

set family, linear algebra method, oddtown, extremal combinatorics
-/

@[expose] public section

open Finset Matrix

variable {α ι K : Type*}

section LinearIndependence

/-- A family of vectors whose pairwise dot products form the identity matrix is linearly
independent. This is the engine of the linear algebra method: an "orthonormality" hypothesis
for the standard bilinear form, over an arbitrary field, with no positivity available. -/
theorem linearIndependent_of_dotProduct_eq_ite [Fintype α] [Field K] [DecidableEq ι]
    {v : ι → α → K} (h : ∀ i j, v i ⬝ᵥ v j = if i = j then 1 else 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  have key : (∑ i ∈ s, g i • v i) ⬝ᵥ v j = ∑ i ∈ s, g i * (v i ⬝ᵥ v j) := by
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hg] at key
  simp only [zero_dotProduct] at key
  rw [Finset.sum_eq_single j] at key
  · simpa [h j j] using key.symm
  · exact fun i _ hij ↦ by simp [h i j, hij]
  · exact fun hjs ↦ absurd hj hjs

end LinearIndependence

namespace Finset

section CharVec

variable [DecidableEq α]

/-- The characteristic vector of a finset `s`, valued in a semiring: it is `1` on `s` and `0`
elsewhere. -/
def charVec [Zero K] [One K] (s : Finset α) : α → K := fun a ↦ if a ∈ s then 1 else 0

@[simp]
theorem charVec_apply [Zero K] [One K] (s : Finset α) (a : α) :
    charVec (K := K) s a = if a ∈ s then 1 else 0 := rfl

/-- The dot product of the characteristic vectors of `s` and `t` counts their intersection. -/
theorem charVec_dotProduct_charVec [Fintype α] [Semiring K] (s t : Finset α) :
    charVec (K := K) s ⬝ᵥ charVec (K := K) t = #(s ∩ t) := by
  have h : ∀ a : α, (if a ∈ s then (1 : K) else 0) * (if a ∈ t then (1 : K) else 0)
      = if a ∈ s ∩ t then (1 : K) else 0 := by
    intro a; by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [hs, ht]
  simp only [dotProduct, charVec_apply, h, Finset.sum_boole]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

end CharVec

section Oddtown

variable [Fintype α] [DecidableEq α]

/-- **Oddtown theorem** (Berlekamp). A family of finsets of odd cardinality, any two distinct
members of which meet in an even number of elements, has at most `Fintype.card α` members.

The proof is the standard linear algebra argument: over `ZMod 2` the hypotheses say exactly
that the Gram matrix of the characteristic vectors is the identity, so those vectors are
linearly independent and there can be at most `Fintype.card α` of them. -/
theorem card_le_card_of_odd_card_of_even_card_inter {𝒜 : Finset (Finset α)}
    (hodd : ∀ s ∈ 𝒜, Odd #s) (heven : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even #(s ∩ t)) :
    #𝒜 ≤ Fintype.card α := by
  classical
  have hgram : ∀ s t : {x // x ∈ 𝒜},
      charVec (K := ZMod 2) s.1 ⬝ᵥ charVec (K := ZMod 2) t.1 = if s = t then 1 else 0 := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    rw [charVec_dotProduct_charVec]
    by_cases hst : s = t
    · subst hst
      rw [Finset.inter_self, ← ZMod.natCast_mod, Nat.odd_iff.mp (hodd s hs)]
      simp
    · rw [← ZMod.natCast_mod, Nat.even_iff.mp (heven s hs t ht hst)]
      simp [Subtype.ext_iff, hst]
  have hind := linearIndependent_of_dotProduct_eq_ite
    (v := fun s : {x // x ∈ 𝒜} ↦ charVec (K := ZMod 2) s.1) hgram
  calc #𝒜 = Fintype.card {x // x ∈ 𝒜} := (Fintype.card_coe 𝒜).symm
    _ ≤ Module.finrank (ZMod 2) (α → ZMod 2) := LinearIndependent.fintype_card_le_finrank hind
    _ = Fintype.card α := Module.finrank_fintype_fun_eq_card (ZMod 2)

end Oddtown

end Finset
