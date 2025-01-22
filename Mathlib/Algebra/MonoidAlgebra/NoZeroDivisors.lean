/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Variations on non-zero divisors in `AddMonoidAlgebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `R[A]` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

In this file we show that if `R` satisfies `NoZeroDivisors` and `A` is a grading type satisfying
`UniqueProds A` (resp. `UniqueSums A`), then `MonoidAlgebra R A` (resp. `R[A]`)
also satisfies `NoZeroDivisors`.

Because of the instances to `UniqueProds/Sums`, we obtain a formalization of the well-known result
that if `R` is a field and `A` is a left-ordered group, then `R[A]` contains no non-zero
zero-divisors.
The actual assumptions on `R` are weaker.

##  Main results

* `MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul` and
  `AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd`
  general sufficient results stating that certain monomials in a product have as coefficient a
  product of coefficients of the factors.
* The instance showing that `Semiring R, NoZeroDivisors R, Mul A, UniqueProds A` imply
  `NoZeroDivisors (MonoidAlgebra R A)`.
* The instance showing that `Semiring R, NoZeroDivisors R, Add A, UniqueSums A` imply
  `NoZeroDivisors R[A]`.

TODO: move the rest of the docs to UniqueProds?
 `NoZeroDivisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `R[A]` has no non-zero zero-divisors.
* `NoZeroDivisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `R[A]` has no non-zero zero-divisors.

The conditions on `A` imposed in `NoZeroDivisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `NoZeroDivisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

* `NoZeroDivisors.biOrdered` shows that if `R` is a semiring with no non-zero zero-divisors,
  `A` has an addition, a linear order and both addition on the left and addition on the right are
  strictly monotone functions, then `AddMonoidAlgebra R A` has no non-zero zero-divisors.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.


###  Remarks
To prove `NoZeroDivisors.biOrdered`,
we use `CovariantClass` assumptions on `A`.  In combination with `LinearOrder A`, these
assumptions actually imply that `A` is cancellative.  However, cancellativity alone in not enough.
Indeed, using `ZMod 2`, that is `ℤ / 2 ℤ`, as the grading type `A`, there are examples of
`AddMonoidAlgebra`s containing non-zero zero divisors:
```lean
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic

open Finsupp AddMonoidAlgebra

example {R} [Ring R] [Nontrivial R] :
  ∃ x y : AddMonoidAlgebra R (ZMod 2), x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0 := by
  --  use `[1 (mod 2)] - 1` and `[1 (mod 2)] + 1`, the rest is easy
  refine ⟨of' _ _ 1 - AddMonoidAlgebra.single 0 1, of' _ _ 1 +  AddMonoidAlgebra.single 0 1, ?_, ?_⟩
  · simp [sub_mul, mul_add, single_mul_single, sub_eq_zero]; rfl
  · simp only [of'_apply, sub_eq_add_neg, ne_eq, ← eq_neg_iff_add_eq_zero.not, neg_neg]
    rw [← Finsupp.single_neg, single_eq_single_iff, single_eq_single_iff]
    simp
```
In this case, the grading type is the additive monoid `ZMod 2` which is an abelian group
(and, in particular, it is cancellative).
-/

open Finsupp

variable {R A : Type*} [Semiring R]

namespace MonoidAlgebra

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_mul_eq_mul_of_uniqueMul [Mul A] {f g : MonoidAlgebra R A} {a0 b0 : A}
    (h : UniqueMul f.support g.support a0 b0) :
    (f * g) (a0 * b0) = f a0 * g b0 := by
  classical
  simp_rw [mul_apply, sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (a0, b0) ?_ ?_).trans (if_pos rfl) <;> simp_rw [Finset.mem_product]
  · refine fun ab hab hne => if_neg (fun he => hne <| Prod.ext ?_ ?_)
    exacts [(h hab.1 hab.2 he).1, (h hab.1 hab.2 he).2]
  · refine fun hnmem => ite_eq_right_iff.mpr (fun _ => ?_)
    rcases not_and_or.mp hnmem with af | bg
    · rw [not_mem_support_iff.mp af, zero_mul]
    · rw [not_mem_support_iff.mp bg, mul_zero]

instance instNoZeroDivisorsOfUniqueProds [NoZeroDivisors R] [Mul A] [UniqueProds A] :
    NoZeroDivisors (MonoidAlgebra R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} ab := by
    contrapose! ab
    obtain ⟨da, a0, db, b0, h⟩ := UniqueProds.uniqueMul_of_nonempty
      (support_nonempty_iff.mpr ab.1) (support_nonempty_iff.mpr ab.2)
    refine support_nonempty_iff.mp ⟨da * db, ?_⟩
    rw [mem_support_iff] at a0 b0 ⊢
    exact mul_apply_mul_eq_mul_of_uniqueMul h ▸ mul_ne_zero a0 b0

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_uniqueAdd [Add A] {f g : R[A]} {a0 b0 : A}
    (h : UniqueAdd f.support g.support a0 b0) :
    (f * g) (a0 + b0) = f a0 * g b0 :=
  MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul (A := Multiplicative A) h

instance [NoZeroDivisors R] [Add A] [UniqueSums A] : NoZeroDivisors R[A] :=
  MonoidAlgebra.instNoZeroDivisorsOfUniqueProds (A := Multiplicative A)


section Covariant_lt
variable [Add A]

section PartialOrder
variable [PartialOrder A] [AddLeftStrictMono A] {a t b : A}
  {f g : AddMonoidAlgebra R A}

/--  The "top" element of `AddMonoidAlgebra.single a r * f` is the product of `r` and
the "top" element of `f`.  Here, "top" is simply an upper bound for the elements
of the support of `f` (e.g. the product is `0` if "top" is not a maximum).
The corresponding statement for a general product `f * g` is `AddMonoidAlgebra.mul_apply_of_le`.
It is proved with a further `CovariantClass` assumption. -/
theorem single_mul_apply_of_le (r : R) (ft : ∀ a ∈ f.support, a ≤ t) :
    ((AddMonoidAlgebra.single a r) * f) (a + t) = r * f t := by
  rw [AddMonoidAlgebra.single_mul_apply_aux]
  intro t' ht'
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  specialize ft t' ht'
  contrapose h
  exact add_lt_add_left (ft.lt_of_ne h) a |>.ne

/--  The "bottom" element of `Finsupp.single a r * f` is the product of `r` and
the "bottom" element of `f`.  Here, "bottom" is simply a lower bound for the elements
of the support of `f` (e.g. the product is `0` if "bottom" is not a minimum).
The corresponding statement for a general product `f * g` is `AddMonoidAlgebra.mul_apply_of_le'`.
It is proved with a further `CovariantClass` assumption. -/
theorem single_mul_apply_of_le' (r : R) (fb : ∀ a ∈ f.support, b ≤ a) :
    ((AddMonoidAlgebra.single a r) * f) (a + b) = r * f b :=
  single_mul_apply_of_le (A := Aᵒᵈ) _ fb

variable [AddRightStrictMono A]

/--  The "top" element of `f * g` is the product of the "top" elements of `f` and of `g`.
Here, "top" is simply an upper bound for the elements of the support of the corresponding
polynomial (e.g. the product is `0` if "top" is not a maximum). -/
theorem mul_apply_of_le (fa : ∀ i ∈ f.support, i ≤ a) (gt : ∀ i ∈ g.support, i ≤ t) :
    (f * g) (a + t) = f a * g t := by
  classical
  nth_rw 1 [← f.erase_add_single a]
  rw [add_mul, Finsupp.add_apply, single_mul_apply_of_le _ gt]
  convert zero_add _
  refine Finsupp.not_mem_support_iff.mp (fun h ↦ ?_)
  refine not_not.mpr ((support_mul _ g) h) ?_
  simp only [Finsupp.support_erase, Finset.mem_biUnion, Finset.mem_erase, ne_eq,
    Finset.mem_singleton, exists_prop, not_exists, not_and, and_imp, Finset.mem_add]
  haveI : AddLeftMono A := addLeftMono_of_addLeftStrictMono A
  exact fun x xa xf y yg ↦ (add_lt_add_of_lt_of_le ((fa _ xf).lt_of_ne xa) (gt _ yg)).ne

/--  The "bottom" element of `f * g` is the product of the "bottom" elements of `f` and of `g`.
Here, "bottom" is simply a lower bound for the elements of the support of the corresponding
polynomial (e.g. the product is `0` if "bottom" is not a minimum). -/
theorem mul_apply_of_le' (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b ≤ i) :
    (f * g) (a + b) = f a * g b :=
  mul_apply_of_le (A := Aᵒᵈ) fa gb

theorem mul_apply_eq_zero_of_lt (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b < i) :
    (f * g) (a + b) = 0 := by
  rw [mul_apply_of_le' fa (fun x hx ↦ ((gb _ hx).le))]
  convert mul_zero _
  exact Finsupp.not_mem_support_iff.mp (fun bg ↦ (lt_irrefl b (gb b bg)).elim)

end PartialOrder

section LinearOrder
variable [NoZeroDivisors R] [LinearOrder A] [AddRightStrictMono A] [AddLeftStrictMono A]

protected theorem NoZeroDivisors.biOrdered : NoZeroDivisors (AddMonoidAlgebra R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} fg := by
    contrapose! fg
    apply_fun (fun x ↦ x (f.support.max' (Finsupp.support_nonempty_iff.mpr fg.1)
      + g.support.max' (Finsupp.support_nonempty_iff.mpr fg.2)))
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    rw [mul_apply_of_le] <;>
      try exact Finset.le_max' _
    refine mul_ne_zero_iff.mpr ⟨?_, ?_⟩ <;>
      exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)

end LinearOrder

end Covariant_lt

end AddMonoidAlgebra
