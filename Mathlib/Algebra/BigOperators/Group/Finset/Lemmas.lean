/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Ring.Parity

/-!
# Miscellaneous lemmas on big operators

The lemmas in this file have been moved out of
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` to reduce its imports.
-/

variable {ι κ M N β : Type*}

@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι) :
    ⇑(∏ x ∈ s, f x) = ∏ x ∈ s, ⇑(f x) :=
  map_prod (MonoidHom.coeFn M N) _ _

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → M → N` -/
@[to_additive (attr := simp)
  /-- See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → M → N` -/]
theorem MonoidHom.finset_prod_apply [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι)
    (b : M) : (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b :=
  map_prod (MonoidHom.eval b) _ _

namespace Finset

variable [CommMonoid M]

open Function in
@[to_additive]
lemma mulSupport_prod (s : Finset ι) (f : ι → κ → M) :
    mulSupport (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, notMem_mulSupport]
  exact fun x ↦ prod_eq_one

@[to_additive]
lemma isSquare_prod {s : Finset ι} (f : ι → M) (h : ∀ c ∈ s, IsSquare (f c)) :
    IsSquare (∏ i ∈ s, f i) := by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

/-- Double the range of a `Finset.sum` -/
@[to_additive]
theorem prod_range_even (n : ℕ) (f : ℕ → M) :
    ∏ k ∈ range n, f k = ∏ k ∈ range (2 * n), if Even k then f (k / 2) else 1 := by
  induction n with
  | zero => simp
  | succ n h => simp [prod_range_succ, h, Nat.mul_add_one]

end Finset
