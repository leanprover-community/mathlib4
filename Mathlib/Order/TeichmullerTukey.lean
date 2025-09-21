/-
Copyright (c) 2025 Ansar Azhdarov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azhdarov
-/
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn

/-!
# Teichmuller-Tukey

This file defines the notion of being of finite character for a family of sets and proves the
Teichmuller-Tukey lemma.

## Main definitions

- `IsOfFiniteCharacter` : A family of sets $F$ is of finite character iff for every set $X$,
  $X ∈ F$ iff every finite subset of $X$ is in $F$.

## Main results

- `IsOfFiniteCharacter.exists_maximal` : Teichmuller-Tukey lemma, saying that every nonempty
  family of finite character has a maximal element.

## References

- <https://en.wikipedia.org/wiki/Teichm%C3%BCller%E2%80%93Tukey_lemma>
-/

open Set Finite

variable {α : Type*} (F : Set (Set α))

namespace Order

/-- A family of sets $F$ is of finite character iff for every set $X$, $X ∈ F$ iff every finite
subset of $X$ is in $F$ -/
def IsOfFiniteCharacter := ∀ x, x ∈ F ↔ ∀ y ⊆ x, y.Finite → y ∈ F

/-- **Teichmuller-Tukey lemma**. Every nonempty family of finite character has a maximal element. -/
theorem IsOfFiniteCharacter.exists_maximal {F} (hF : IsOfFiniteCharacter F) {x : Set α}
    (xF : x ∈ F) : ∃ m, x ⊆ m ∧ Maximal (· ∈ F) m := by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne ↦
    ⟨sUnion c, ?_, fun s sc ↦ subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to `F`. -/
  refine (hF (sUnion c)).mpr fun s sc sfin ↦ ?_
  /- Use the finite character property and the fact that any finite subset of the union is also a
  subset of some element of the chain. -/
  obtain ⟨t, tc, st⟩ := cch.directedOn.exists_mem_subset_of_finite_of_subset_sUnion cne sfin sc
  exact (hF t).mp (cF tc) s st sfin

end Order
