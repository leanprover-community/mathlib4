/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Geometry.Group.WordProd

/-!
# The word metric

The word length of an element is the length of a shortest representing word, over a generating
family given by `Group.Generators`, and the word metric is the distance it induces on `G`. The
resulting object is `NormGroup G` with `dist g h = ‖g⁻¹ * h‖`.

## Main definitions

* `Group.Generators.wordLength`: the word length of an element of `G` with respect to a
  generating family `P`.
* `Group.Generators.IsGeodesic`: a word is geodesic if of minimal length among the words
  representing the same group element.
* `Group.Generators.wordNorm`: the word length as a norm on `G`.
* `Group.Generators.normedGroup`: the normed group structure on `G` induced by `wordNorm`.
  This gives rise to a word metric on `G`.

## Main results

* `Group.Generators.exists_isGeodesic`: every element of `G` is represented by some geodesic
  word.

## Implementation notes

* The API in this file is modelled on the length API for Coxeter groups (`CoxeterSystem.length`).
* The definition of `wordLength` uses `sInf` as `InfSet ℕ` already uses `Nat.find`, saving us from
  having to rewrite `classical`. The junk value `0` on `∅` is never reached because every group
  element has at least one word representing it. It uses `@[no_expose]` as it has no useful defeqs.

## TODO
* Bridge the word metric to the distance in the Cayley graph.

## Tags

word metric, word length, geometric group theory

-/

@[expose] public section

namespace Group.Generators

variable {G ι : Type*} [Group G]

variable (P : Group.Generators G ι) (g h : G) (l : List (ι × Bool))

/-! ### The word length -/

/-- The word length of `g` with respect to the generating family `P`. -/
@[no_expose]
noncomputable def wordLength : ℕ := sInf {n | ∃ l, P.wordProd l = g ∧ l.length = n}

/-- The word length of a group element given by a word `l` is smaller or equal to the
length of `l`. -/
lemma wordLength_wordProd_le : P.wordLength (P.wordProd l) ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, rfl⟩

/-! ### Geodesic words -/

/-- A word `l` is geodesic if its length is exactly the word length of the group element it
represents. -/
def IsGeodesic : Prop := P.wordLength (P.wordProd l) = l.length

lemma IsGeodesic.eq {l : List (ι × Bool)} (hl : P.IsGeodesic l) :
    P.wordLength (P.wordProd l) = l.length := hl

/-- Every group element has a geodesic word representative. -/
theorem exists_isGeodesic : ∃ l, P.IsGeodesic l ∧ P.wordProd l = g := by
  obtain ⟨l, rfl, hlen⟩ := Nat.sInf_mem (Set.Nonempty.image List.length (P.wordProd_surjective g))
  exact ⟨l, hlen.symm, rfl⟩

/-! ### Word length -/

@[simp]
lemma wordLength_one : P.wordLength (1 : G) = 0 := eq_zero_of_nonpos (P.wordLength_wordProd_le [])

@[simp]
lemma wordLength_eq_zero_iff : P.wordLength g = 0 ↔ g = 1 := by
  constructor
  · obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
    intro h
    rw [hl.eq, List.length_eq_zero_iff] at h
    exact h ▸ P.wordProd_nil
  · intro h
    exact h ▸ P.wordLength_one

-- This is superceded by `wordLength_inv`.
private lemma wordLength_inv_le : P.wordLength g⁻¹ ≤ P.wordLength g := by
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
  simpa [wordProd_invRev, hl.eq] using P.wordLength_wordProd_le (FreeGroup.invRev l)

@[simp]
lemma wordLength_inv : P.wordLength g⁻¹ = P.wordLength g := by
  apply le_antisymm
  · exact P.wordLength_inv_le g
  · simpa using P.wordLength_inv_le g⁻¹

lemma wordLength_mul_le : P.wordLength (g * h) ≤ P.wordLength g + P.wordLength h := by
  obtain ⟨l₁, hl₁, rfl⟩ := P.exists_isGeodesic g
  obtain ⟨l₂, hl₂, rfl⟩ := P.exists_isGeodesic h
  simpa [wordProd_append, hl₁.eq, hl₂.eq] using P.wordLength_wordProd_le (l₁ ++ l₂)

/-- The `wordLength` with respect to a generating family `P` defines a norm on `G`. -/
noncomputable def groupNorm : GroupNorm G where
  toFun g := P.wordLength g
  map_one' := by simp
  mul_le' g h := by exact_mod_cast P.wordLength_mul_le g h
  inv' g := by simp
  eq_one_of_map_eq_zero' g hg := by simpa using hg

/-! ### Word metric -/

/-- `G` as a metric space `NormedGroup G` with respect to a generating family `P`, given by
`dist g h = ‖g⁻¹ * h‖`. -/
@[instance_reducible]
noncomputable def normedGroup : NormedGroup G := P.groupNorm.toNormedGroup

end Group.Generators
