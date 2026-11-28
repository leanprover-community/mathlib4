/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic

import Mathlib.Algebra.Homology.HomologicalComplex

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Boundary of an embedding of complex shapes

In the file `Mathlib/Algebra/Homology/Embedding/Basic.lean`, given `p : ℤ`, we have defined
an embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ` in `ComplexShape.up ℤ`
which sends `n : ℕ` to `p + n`. The (canonical) truncation (`≥ p`) of
`K : CochainComplex C ℤ` shall be defined as the extension to `ℤ`
(see `Mathlib/Algebra/Homology/Embedding/Extend.lean`) of
a certain cochain complex indexed by `ℕ`:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). In this case,
we see that the degree `0 : ℕ` needs a particular attention when
constructing the truncation.

In this file, more generally, for `e : Embedding c c'`, we define
a predicate `ι → Prop` named `e.BoundaryGE` which shall be relevant
when constructing the truncation `K.truncGE e` when `e.IsTruncGE`.
In the case of `embeddingUpIntGE p`, we show that `0 : ℕ` is the
only element in this lower boundary. Similarly, we define
`Embedding.BoundaryLE`.
-/

@[expose] public section

namespace ComplexShape

namespace Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

to_dual_name_hint GE LE

/-- The lower boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `i' : ι'` not in the image of `e.f`
such that `c'.Rel i' (e.f j)`. -/
@[to_dual
/-- The upper boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `k' : ι'` not in the image of `e.f`
such that `c'.Rel (e.f j) k'`. -/]
def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ ∀ i, ¬c'.Rel (e.f i) (e.f j)

@[to_dual]
lemma boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : ∀ i, e.f i ≠ i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj, c'.prev_eq' hi]

@[to_dual]
lemma not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

@[to_dual]
lemma not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

variable {e} in
@[to_dual]
lemma BoundaryGE.notMem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

@[to_dual]
lemma prev_f_of_not_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
    (hj : ¬ e.BoundaryGE j) :
    c'.prev (e.f j) = e.f i := by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj hj'
    rw [e.rel_iff] at hi
    rw [c.prev_eq' hi] at hij
    exact hij' (by simpa only [hij] using hi)

variable {e} in
@[to_dual]
lemma BoundaryGE.false_of_isTruncLE {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

@[to_dual]
lemma next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.f k := by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk', e.rel_iff] at hj
    rw [← hk', ← c.next_eq' hj, hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [c'.next_eq' hj'] using hj'

@[to_dual (attr := simp)]
lemma op_boundaryLE_iff {j : ι} : e.op.BoundaryLE j ↔ e.BoundaryGE j := by rfl

end Embedding

lemma boundaryGE_embeddingUpIntGE_iff (p : ℤ) (n : ℕ) :
    (embeddingUpIntGE p).BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

lemma boundaryLE_embeddingUpIntLE_iff (p : ℤ) (n : ℕ) :
    (embeddingUpIntLE p).BoundaryLE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

end ComplexShape
