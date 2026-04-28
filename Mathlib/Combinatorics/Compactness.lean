/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Set.Finite.Basic

/-!
# Combinatorial compactness and the Rado selection lemma

This file contains compactness arguments for constructing infinite objects from finite
approximations. The main result is a formalization of Rado's selection principle, as an application
of compactness to combinatorics.

We give four versions, depending on whether the "partial" functions are defined locally or globally,
and whether we use `Finset` or `Set.Finite`. The precise formulation of the lemma is therefore
`Finset.rado_selection_subtype` or `Set.Finite.rado_selection_subtype`, but the versions avoiding
subtypes are easier to prove and often easier to apply, so they are provided too.

## Main results

* `Finset.rado_selection`: Given functions `g : Finset α → α → β` where `β` is finite,
  there exists a single function `χ : α → β` which is constructed out of `g`.
  More precisely, for each finite set `s`, there exists a larger set `t ⊇ s` such that
  `χ` and `g t` agree on `s`.
  In fact, we can more generally allow each `g s` to be a dependent function, as `(a : α) → β a`, so
  the type of `g` will be `Finset α → (a : α) → β a`.

* `Finset.rado_selection_subtype`: A variant where `g` takes elements in the subtype.

* `Set.Finite.rado_selection`: A variant using `Set.Finite`.

* `Set.Finite.rado_selection`: A variant using `Set.Finite` and where `g` takes elements in the
  subtype.

## Implementation notes

The proof uses the fact that the product of finite discrete spaces is compact
(by Tychonoff's theorem). The closed sets corresponding to "agreeing with `g s` on `s`"
have the finite intersection property, so their intersection is nonempty.

## References

* de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs and a problem
  in the theory of relations".
* Rado, R. (1949). "Axiomatic treatment of rank in infinite sets".

-/

public section

variable {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]

/--
Given a (dependent) function `g s : (a : α) → β a` for each finset `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection (g : Finset α → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by
  classical
  let instTop (a : α) : TopologicalSpace (β a) := ⊥
  have instDiscr (a : α) : DiscreteTopology (β a) := discreteTopology_bot _
  let e (s : Finset α) : Set ((a : α) → β a) := {f | ∃ t, s ⊆ t ∧ ∀ x ∈ s, f x = g t x}
  have (s : Finset α) : s.restrict ⁻¹' {f | ∃ t, s ⊆ t ∧ ∀ x, f x = g t x} = e s := by simp [e]
  have he' (s : Finset α) : IsClosed (e s) := by
    rw [← this]
    exact (isClosed_discrete _).preimage (by fun_prop)
  have he'' (B : Finset (Finset α)) : (⋂ i ∈ B, e i).Nonempty := by
    refine ⟨g (B.biUnion id), ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq, e]
    intro i hi
    exact ⟨_, subset_biUnion_of_mem id hi, by simp⟩
  simpa using CompactSpace.iInter_nonempty he' he''

/--
Given a (dependent) function `g s : (a : s) → β a` for each finset `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection_subtype (g : (s : Finset α) → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α,
      ∃ (t : Finset α) (hst : s ⊆ t), ∀ x : s, χ x = g t (Set.inclusion hst x) := by
  classical
  have (a : α) : Nonempty (β a) := ⟨g {a} ⟨a, by simp⟩⟩
  let g' (s) (a : α) : β a := if ha : a ∈ s then g s ⟨a, ha⟩ else Classical.arbitrary (β a)
  have hg (s : Finset α) (x : s) : g s x = g' s x := by simp [g']
  simpa [hg] using Finset.rado_selection g'

/--
Given a (dependent) function `g s : (a : α) → β a` for each finite set `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection (g : (s : Set α) → s.Finite → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite), s ⊆ t ∧ ∀ x ∈ s, χ x = g t ht x := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, ht'⟩ := hχ hs.toFinset
  exact ⟨t, by simp_all⟩

/--
Given a (dependent) function `g s : (a : s) → β a` for each finite set `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection_subtype (g : (s : Set α) → s.Finite → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite) (hst : s ⊆ t), ∀ x : s, χ x = g t ht (Set.inclusion hst x) := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection_subtype (β := β) (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hst⟩ := hχ hs.toFinset
  simp only [Set.Finite.toFinset_subset] at ht
  exact ⟨t, by simp_all⟩

end
