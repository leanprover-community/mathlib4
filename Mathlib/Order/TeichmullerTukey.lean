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

- `exists_maximal_of_isOfFiniteCharacter` : Teichmuller-Tukey lemma, saying that every nonempty
  family of finite character has a maximal element.

## References

- <https://en.wikipedia.org/wiki/Teichm%C3%BCller%E2%80%93Tukey_lemma>
-/

open Set Finite

variable {α : Type*} (F : Set (Set α))

/-- A family of sets $F$ is of finite character iff for every set $X$, $X ∈ F$ iff every finite
subset of $X$ is in $F$ -/
def IsOfFiniteCharacter := ∀ x, x ∈ F ↔ ∀ y ⊆ x, y.Finite → y ∈ F

lemma DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion {c : Set (Set α)}
    (cne : c.Nonempty) (cdir : DirectedOn (· ⊆ ·) c) {s : Set α} (sc : s ⊆ sUnion c)
    (sfin : s.Finite) : ∃ t ∈ c, s ⊆ t := by
  rw [← sfin.coe_toFinset, sUnion_eq_biUnion] at sc
  have := DirectedOn.exists_mem_subset_of_finset_subset_biUnion cne cdir sc
  exact sfin.coe_toFinset ▸ this

lemma IsChain.exists_mem_subset_of_finite_of_subset_sUnion {c : Set (Set α)}
    (cne : c.Nonempty) (cch : IsChain (· ⊆ ·) c) {s : Set α} (sc : s ⊆ sUnion c) (sfin : s.Finite) :
    ∃ t ∈ c, s ⊆ t := DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
      cne cch.directedOn sc sfin

/-- **Teichmuller-Tukey lemma**. Every nonempty family of finite character has a maximal element. -/
theorem exists_maximal_of_isOfFiniteCharacter {F} (hF : IsOfFiniteCharacter F) {x : Set α}
    (xF : x ∈ F) : ∃ m, x ⊆ m ∧ Maximal (· ∈ F) m := by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne ↦
    ⟨sUnion c, ?_, fun s sc ↦ subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to F. Use the finite character property and the fact that any
  finite subset of the union is also a subset of some element of the chain. -/
  refine (hF (sUnion c)).mpr (fun s sc sfin ↦ ?_)
  obtain ⟨t, tc, st⟩ := cch.exists_mem_subset_of_finite_of_subset_sUnion cne sc sfin
  exact (hF t).mp (cF tc) s st sfin
