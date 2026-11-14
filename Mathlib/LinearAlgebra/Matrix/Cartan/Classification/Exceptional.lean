/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Classification.Leaf

/-!
# The classification step for types `F₄` and `G₂`

Attaching a leaf to `F₄` or `G₂` never gives a finite Cartan matrix: either some node or some
two-node path carries four or more bonds, or the result contains the affine diagram of type `F₄`.

## Main results

* `Matrix.not_isFiniteCartan_addLeaf_F₄`: attaching a leaf to `F₄` gives no finite Cartan matrix.
* `Matrix.not_isFiniteCartan_addLeaf_G₂`: attaching a leaf to `G₂` gives no finite Cartan matrix.
-/

public section

open CartanMatrix

namespace Matrix

/-- Attaching a leaf to `F₄`, with any bond, never gives a finite Cartan matrix. -/
theorem not_isFiniteCartan_addLeaf_F₄ (u : Fin 4) {a b : ℤ} (hab : IsBond a b) :
    ¬ (addLeaf F₄ u a b).IsFiniteCartan := by
  intro h
  fin_cases u
  · obtain ⟨rfl, rfl⟩ | hab := hab.eq_neg_one_or_two_le_mul
    -- u = 0, simple bond: null vector of affine F₄ on last, 0, 1, 2, 3
    · exact h.mulVec_ne_zero (f := ![4, 0, 1, 2, 3]) (by decide) (x := ![1, 2, 3, 2, 1])
        (by decide) (by decide)
    -- u = 0, multiple bond: path 0, 1 has bonds with last (at 0) and 2 (at 1)
    · have := h.path_bonds_lt_four ![0, 1] (by decide) (by simp [addLeaf, F₄]) [(0, 4), (1, 2)]
        (by decide) (by decide)
      simp [addLeaf, F₄] at this
      lia
  -- u = 1: bonds at 1 with 0, 2 and last
  · have := h.bonds_lt_four 1 [0, 2, 4] (by decide)
    simp [addLeaf, F₄] at this
    linarith [hab.one_le_mul]
  -- u = 2: bonds at 2 with 1, 3 and last
  · have := h.bonds_lt_four 2 [1, 3, 4] (by decide)
    simp [addLeaf, F₄] at this
    linarith [hab.one_le_mul]
  · obtain ⟨rfl, rfl⟩ | hab := hab.eq_neg_one_or_two_le_mul
    -- u = 3, simple bond: null vector of affine F₄ on 0, 1, 2, 3, last
    · exact h.mulVec_ne_zero (f := ![0, 1, 2, 3, 4]) (by decide) (x := ![2, 4, 3, 2, 1])
        (by decide) (by decide)
    -- u = 3, multiple bond: path 2, 3 has bonds with 1 (at 2) and last (at 3)
    · have := h.path_bonds_lt_four ![2, 3] (by decide) (by simp [addLeaf, F₄]) [(0, 1), (1, 4)]
        (by decide) (by decide)
      simp [addLeaf, F₄] at this
      lia

/-- Attaching a leaf to `G₂`, with any bond, never gives a finite Cartan matrix. -/
theorem not_isFiniteCartan_addLeaf_G₂ (u : Fin 2) {a b : ℤ} (hab : IsBond a b) :
    ¬ (addLeaf G₂ u a b).IsFiniteCartan := by
  intro h
  -- triple bond between 0 and 1, plus the bond from u to last: four bonds at u
  have := h.bonds_lt_four u.castSucc [(1 - u).castSucc, Fin.last 2] (by fin_cases u <;> decide)
  fin_cases u <;> simp [addLeaf, G₂] at this <;> linarith [hab.one_le_mul]

end Matrix
