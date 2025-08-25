/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
#  Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f a ≠ 0`.

## TODO

The following lemma is currently missing since it needs:
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

theorem support_single_mul_eq_image [DecidableEq G] (f : SkewMonoidAlgebra k G) {r : k}
    {x : G} (lx : IsLeftRegular x) (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_mul, ite_self, sum_zero, lx.eq_iff]

theorem support_mul_single_eq_image [DecidableEq G] (f : SkewMonoidAlgebra k G) {r : k} {x : G}
    (rx : IsRightRegular x) (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    ite_self, rx.eq_iff]

theorem support_mul_single [IsRightCancelMul G] (f : SkewMonoidAlgebra k G) (r : k) (x : G)
   (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
    ext
    simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]

theorem support_single_mul [IsLeftCancelMul G] (f : SkewMonoidAlgebra k G) (r : k) (x : G)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
    ext
    simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

end Semiring

end SkewMonoidAlgebra
