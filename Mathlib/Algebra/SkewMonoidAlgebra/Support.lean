/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
#  Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f a ≠ 0`.

## TODO

The following lemmas are currently missing:
- `support_single_mul_eq_image`
- `support_mul_single_eq_image`
- `support_mul_single`
- `support_single_mul`
- `mem_span_support`
-/

open scoped Pointwise

universe u₁ u₂ u₃

namespace SkewMonoidAlgebra

open Finset Finsupp

variable {k : Type u₁} {G : Type u₂}

section AddCommMonoid

variable [AddCommMonoid k]

theorem support_single_ne_zero {b : k} (a : G) (h : b ≠ 0) : (single a b).support = {a} := by
  rw [single, support, Finsupp.support_single_ne_zero _ h]

theorem support_single_subset {a : G} {b : k} : (single a b).support ⊆ {a} := by
  rw [single, support]
  exact Finsupp.support_single_subset

theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} :
    (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f.coeff a)).support := by
  simp_rw [support, toFinsupp_sum']
  apply Finsupp.support_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support, toFinsupp_neg, Finsupp.support_neg]
  rfl

end AddCommGroup

section AddCommMonoidWithOne

variable [AddCommMonoidWithOne k]

lemma support_one_subset [One G] : (1 : SkewMonoidAlgebra k G).support ⊆ 1 :=
  Finsupp.support_single_subset

@[simp]
lemma support_one [One G] [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1 :=
  Finsupp.support_single_ne_zero _ one_ne_zero

end AddCommMonoidWithOne

section Semiring

variable [Monoid G] [Semiring k] [MulSemiringAction G k]

theorem support_mul [DecidableEq G] (a b : SkewMonoidAlgebra k G) :
    (a * b).support ⊆ a.support * b.support := by
  rw [mul_def]
  exact support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy

theorem support_single_mul_subset [DecidableEq G] (f : SkewMonoidAlgebra k G) (r : k) (a : G) :
    (single a r * f : SkewMonoidAlgebra k G).support ⊆ Finset.image (a * ·) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_right support_single_subset).trans <| by
    rw [Finset.image₂_singleton_left]

theorem support_mul_single_subset [DecidableEq G] (f : SkewMonoidAlgebra k G) (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_left support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]

end Semiring

end SkewMonoidAlgebra
