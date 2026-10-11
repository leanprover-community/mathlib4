/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.AlgebraicTopology.Reedy.Direct
public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory

/-!
# The semi-simplex category is direct

The category `SemiSimplexCategory` (finite nonempty ordinals and order embeddings) is a direct
category: every non-identity morphism `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` satisfies `n < m`. Hence it has a Reedy
structure `SemiSimplexCategory.reedyStructure` in which `W₁` consists of the identities and
`W₂` of all morphisms, with degree `len`.

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]
-/

@[expose] public section

open CategoryTheory MorphismProperty HomotopicalAlgebra

open scoped Simplicial

namespace SemiSimplexCategory

/-- In `SemiSimplexCategory`, every endomorphism is an identity. -/
lemma eq_id_of_endo {n : SemiSimplexCategory} (f : n ⟶ n) : f = 𝟙 n :=
  toSimplexCategory.map_injective (by
    rw [SimplexCategory.eq_id_of_mono (toSimplexCategory.map f), CategoryTheory.Functor.map_id])

lemma len_le_of_hom {n m : SemiSimplexCategory} (f : n ⟶ m) : n.len ≤ m.len :=
  SimplexCategory.len_le_of_mono (toSimplexCategory.map f)

/-- A morphism of `SemiSimplexCategory` which is not an identity strictly increases `len`. -/
lemma len_lt_of_not_identities {n m : SemiSimplexCategory} (f : n ⟶ m)
    (hf : ¬ identities _ f) : n.len < m.len := by
  refine (len_le_of_hom f).lt_of_ne fun h ↦ hf ?_
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  dsimp at h
  subst h
  rw [eq_id_of_endo f]
  exact .mk _

/-- The Reedy structure making `SemiSimplexCategory` a direct category, with degree `len`. -/
def reedyStructure : ReedyStructure (identities SemiSimplexCategory) ⊤ ℕ where
  deg := len
  lt₁ _ hf hf' := absurd hf hf'
  lt₂ f _ hf' := len_lt_of_not_identities f hf'
  nonempty_unique _ := ⟨inferInstance⟩

end SemiSimplexCategory
