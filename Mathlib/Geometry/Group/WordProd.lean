/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Generators

/-!
# Evaluation of words

A generating family `P : Group.Generators G ι` indexed by `ι` gives rise to an evaluation map
`P.wordProd : List (ι × Bool) → G`.

## Main definitions

* `Group.Generators.wordProd`: the canonical map from a word `List (ι × Bool)` over a generating
  family `ι` to the corresponding group `G`. It sends each `(i, true)` to `P.val i` and
  `(i, false)` to `(P.val i)⁻¹`.

## Implementation notes

* The API in this file is modelled on the word API for Coxeter groups (`CoxeterSystem.wordProd`).
* `List (ι × Bool)` is the canonical way to write words which evaluate to `FreeGroup` elements
  through `FreeGroup.mk`.

## Tags

word, generating set, geometric group theory
-/

@[expose] public section

variable {G ι : Type*} [Group G]

namespace Group.Generators

variable (P : Group.Generators G ι) (i : ι) (b : Bool) (l l₁ l₂ : List (ι × Bool))

/-- The canonical map from a word `List (ι × Bool)` over a generating family `ι` to its
corresponding group `G`. -/
def wordProd : G := P.lift (FreeGroup.mk l)

/-- Every element of `G` is the product of some word over a generating family. -/
theorem wordProd_surjective : Function.Surjective P.wordProd :=
  P.lift_surjective.comp Quot.mk_surjective

@[simp]
lemma wordProd_nil : P.wordProd [] = 1 := by
  simp [wordProd]

@[simp]
lemma wordProd_singleton : P.wordProd [(i, b)] = cond b (P.val i) (P.val i)⁻¹ := by
  simp [wordProd]

lemma wordProd_cons : P.wordProd ((i, b) :: l) = cond b (P.val i) (P.val i)⁻¹ * P.wordProd l := by
  simp [wordProd]

lemma wordProd_append : P.wordProd (l₁ ++ l₂) = P.wordProd l₁ * P.wordProd l₂ := by
  simp [wordProd]

lemma wordProd_invRev : P.wordProd (FreeGroup.invRev l) = (P.wordProd l)⁻¹ := by
  simp [wordProd, ← FreeGroup.inv_mk]

end Group.Generators
