/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.Algebra.MonoidAlgebra.Opposite

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

## Main results

* `MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul` and
  `AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd`
  general sufficient results stating that certain monomials in a product have as coefficient a
  product of coefficients of the factors.
* The instance showing that `Semiring R, NoZeroDivisors R, Mul A, UniqueProds A` imply
  `NoZeroDivisors (MonoidAlgebra R A)`.
* The instance showing that `Semiring R, NoZeroDivisors R, Add A, UniqueSums A` imply
  `NoZeroDivisors R[A]`.

TODO: move the rest of the docs to UniqueProds?
* `NoZeroDivisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `R[A]` has no non-zero zero-divisors.
* `NoZeroDivisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `R[A]` has no non-zero zero-divisors.

The conditions on `A` imposed in `NoZeroDivisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `NoZeroDivisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
-/

open Finsupp

variable {R A : Type*}

section Semiring
variable [Semiring R]

namespace MonoidAlgebra

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_mul_eq_mul_of_uniqueMul [Mul A] {f g : MonoidAlgebra R A} {a0 b0 : A}
    (h : UniqueMul f.support g.support a0 b0) :
    (f * g) (a0 * b0) = f a0 * g b0 := by
  classical
  simp_rw [mul_apply, sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (a0, b0) ?_ ?_).trans (if_pos rfl) <;> simp_rw [Finset.mem_product]
  · refine fun ab hab hne ↦ if_neg (fun he ↦ hne <| Prod.ext ?_ ?_)
    exacts [(h hab.1 hab.2 he).1, (h hab.1 hab.2 he).2]
  · refine fun hnotMem ↦ ite_eq_right_iff.mpr (fun _ ↦ ?_)
    rcases not_and_or.mp hnotMem with af | bg
    · rw [notMem_support_iff.mp af, zero_mul]
    · rw [notMem_support_iff.mp bg, mul_zero]

instance [NoZeroDivisors R] [Mul A] [UniqueProds A] : NoZeroDivisors (MonoidAlgebra R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} ab := by
    contrapose! ab
    obtain ⟨da, a0, db, b0, h⟩ := UniqueProds.uniqueMul_of_nonempty
      (support_nonempty_iff.mpr ab.1) (support_nonempty_iff.mpr ab.2)
    refine support_nonempty_iff.mp ⟨da * db, ?_⟩
    rw [mem_support_iff] at a0 b0 ⊢
    exact mul_apply_mul_eq_mul_of_uniqueMul h ▸ mul_ne_zero a0 b0

instance [IsCancelAdd R] [IsLeftCancelMulZero R] [Mul A] [UniqueProds A] :
    IsLeftCancelMulZero (MonoidAlgebra R A) where
  mul_left_cancel_of_ne_zero {f} hf {g₁ g₂} eq := by
    classical
    induction hg : g₁.support ∪ g₂.support using Finset.eraseInduction generalizing g₁ g₂ with
    | _ s ih =>
    obtain h | h := s.eq_empty_or_nonempty <;> subst s
    · simp_rw [Finset.union_eq_empty, support_eq_empty] at h; exact h.1.trans h.2.symm
    have ⟨af, haf, ag, hag, uniq⟩ := UniqueProds.uniqueMul_of_nonempty (support_nonempty_iff.2 hf) h
    have h := mul_apply_mul_eq_mul_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_left)
    dsimp only at eq
    rw [eq, mul_apply_mul_eq_mul_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_right)] at h
    have := mul_left_cancel₀ (mem_support_iff.mp haf) h
    rw [← g₁.erase_add_single ag, ← g₂.erase_add_single ag, this] at eq ⊢
    simp_rw [mul_add, add_right_cancel_iff] at eq
    rw [ih ag hag eq]
    simp_rw [support_erase, Finset.erase_union_distrib]

instance [IsCancelAdd R] [IsRightCancelMulZero R] [Mul A] [UniqueProds A] :
    IsRightCancelMulZero (MonoidAlgebra R A) :=
  MulOpposite.isLeftCancelMulZero_iff.mp <|
    MonoidAlgebra.opRingEquiv.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

instance [IsCancelAdd R] [IsCancelMulZero R] [Mul A] [UniqueProds A] :
    IsCancelMulZero (MonoidAlgebra R A) where

instance [IsCancelAdd R] [IsDomain R] [Monoid A] [UniqueProds A] :
    IsDomain (MonoidAlgebra R A) where

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_uniqueAdd [Add A] {f g : R[A]} {a0 b0 : A}
    (h : UniqueAdd f.support g.support a0 b0) :
    (f * g) (a0 + b0) = f a0 * g b0 :=
  MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul (A := Multiplicative A) h

instance [NoZeroDivisors R] [Add A] [UniqueSums A] : NoZeroDivisors R[A] :=
  inferInstanceAs (NoZeroDivisors (MonoidAlgebra R (Multiplicative A)))

instance [IsCancelAdd R] [IsLeftCancelMulZero R] [Add A] [UniqueSums A] :
    IsLeftCancelMulZero R[A] :=
  inferInstanceAs (IsLeftCancelMulZero (MonoidAlgebra R (Multiplicative A)))

instance [IsCancelAdd R] [IsRightCancelMulZero R] [Add A] [UniqueSums A] :
    IsRightCancelMulZero R[A] :=
  inferInstanceAs (IsRightCancelMulZero (MonoidAlgebra R (Multiplicative A)))

instance [IsCancelAdd R] [IsCancelMulZero R] [Add A] [UniqueSums A] : IsCancelMulZero R[A] where

instance [IsCancelAdd R] [IsDomain R] [AddMonoid A] [UniqueSums A] : IsDomain R[A] where

end AddMonoidAlgebra
end Semiring
