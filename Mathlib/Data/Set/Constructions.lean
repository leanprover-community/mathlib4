/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Set.Lattice

/-!
# Constructions involving sets of sets.

## Finite Intersections

We define a structure `FiniteInter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finiteInterClosure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finiteInterClosure S` is endowed with a term of type `FiniteInter` using
`finiteInterClosure_finiteInter`.

-/


variable {α : Type*} (S : Set (Set α))

/-- A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
structure FiniteInter : Prop where
  /-- `univ_mem` states that `Set.univ` is in `S`. -/
  univ_mem : Set.univ ∈ S
  /-- `inter_mem` states that any two intersections of sets in `S` is also in `S`. -/
  inter_mem : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ∩ t ∈ S

namespace FiniteInter

/-- The smallest set of sets containing `S` which is closed under finite intersections. -/
inductive finiteInterClosure : Set (Set α)
  | basic {s} : s ∈ S → finiteInterClosure s
  | univ : finiteInterClosure Set.univ
  | inter {s t} : finiteInterClosure s → finiteInterClosure t → finiteInterClosure (s ∩ t)

theorem finiteInterClosure_finiteInter : FiniteInter (finiteInterClosure S) :=
  { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }

variable {S}

theorem finiteInter_mem (cond : FiniteInter S) (F : Finset (Set α)) :
    ↑F ⊆ S → ⋂₀ (↑F : Set (Set α)) ∈ S := by
  classical
    refine Finset.induction_on F (fun _ => ?_) ?_
    · simp [cond.univ_mem]
    · intro a s _ h1 h2
      suffices a ∩ ⋂₀ ↑s ∈ S by simpa
      exact
        cond.inter_mem (h2 (Finset.mem_insert_self a s))
          (h1 fun x hx => h2 <| Finset.mem_insert_of_mem hx)

theorem finiteInterClosure_insert {A : Set α} (cond : FiniteInter S) (P)
    (H : P ∈ finiteInterClosure (insert A S)) : P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q := by
  induction H with
  | basic h =>
    cases h
    · exact Or.inr ⟨Set.univ, cond.univ_mem, by simpa⟩
    · exact Or.inl (by assumption)
  | univ => exact Or.inl cond.univ_mem
  | @inter T1 T2 _ _ h1 h2 =>
    rcases h1 with (h | ⟨Q, hQ, rfl⟩) <;> rcases h2 with (i | ⟨R, hR, rfl⟩)
    · exact Or.inl (cond.inter_mem h i)
    · exact
        Or.inr ⟨T1 ∩ R, cond.inter_mem h hR, by simp only [← Set.inter_assoc, Set.inter_comm _ A]⟩
    · exact Or.inr ⟨Q ∩ T2, cond.inter_mem hQ i, by simp only [Set.inter_assoc]⟩
    · exact
        Or.inr
          ⟨Q ∩ R, cond.inter_mem hQ hR, by
            ext x
            constructor <;> simp +contextual⟩

open Set

theorem mk₂ (h : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ∩ t ∈ S) :
    FiniteInter (insert (univ : Set α) S) where
  univ_mem := Set.mem_insert Set.univ S
  inter_mem s hs t ht := by aesop

end FiniteInter

/-- This is a hybrid of `Set.biUnion_empty` and `Finset.biUnion_empty` (the index set on the LHS is
the empty finset, but `s` is a family of sets, not finsets). -/
theorem Set.biUnion_empty_finset {ι X : Type*} {s : ι → Set X} :
    ⋃ i ∈ (∅ : Finset ι), s i = ∅ := by
  simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
