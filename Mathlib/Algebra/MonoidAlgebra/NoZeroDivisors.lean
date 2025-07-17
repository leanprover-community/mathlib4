/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs

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

theorem mul_apply_mul_eq_mul_of_uniqueMul_of_subset [Mul A] {f g : MonoidAlgebra R A} {a0 b0 : A}
    {sf sg : Finset A} (hf : f.support ⊆ sf) (hg : g.support ⊆ sg) (h : UniqueMul sf sg a0 b0) :
    (f * g) (a0 * b0) = f a0 * g b0 := by
  classical
  simp_rw [mul_apply, sum, ← Finset.sum_product']
  refine (Finset.sum_eq_single (a0, b0) ?_ ?_).trans (if_pos rfl) <;> simp_rw [Finset.mem_product]
  · refine fun ab hab hne ↦ if_neg (fun he ↦ hne <| Prod.ext ?_ ?_)
    exacts [(h (hf hab.1) (hg hab.2) he).1, (h (hf hab.1) (hg hab.2) he).2]
  · refine fun hnotMem ↦ ite_eq_right_iff.mpr (fun _ ↦ ?_)
    rcases not_and_or.mp hnotMem with af | bg
    · rw [notMem_support_iff.mp af, zero_mul]
    · rw [notMem_support_iff.mp bg, mul_zero]

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_mul_eq_mul_of_uniqueMul [Mul A] {f g : MonoidAlgebra R A} {a0 b0 : A}
    (h : UniqueMul f.support g.support a0 b0) :
    (f * g) (a0 * b0) = f a0 * g b0 :=
  mul_apply_mul_eq_mul_of_uniqueMul_of_subset subset_rfl subset_rfl h

instance instNoZeroDivisorsOfUniqueProds [NoZeroDivisors R] [Mul A] [UniqueProds A] :
    NoZeroDivisors (MonoidAlgebra R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} ab := by
    contrapose! ab
    obtain ⟨da, a0, db, b0, h⟩ := UniqueProds.uniqueMul_of_nonempty
      (support_nonempty_iff.mpr ab.1) (support_nonempty_iff.mpr ab.2)
    refine support_nonempty_iff.mp ⟨da * db, ?_⟩
    rw [mem_support_iff] at a0 b0 ⊢
    exact mul_apply_mul_eq_mul_of_uniqueMul h ▸ mul_ne_zero a0 b0

instance instIsLeftCancelMulZeroOfUniqueProds [IsCancelAdd R] [IsLeftCancelMulZero R] [Mul A]
    [UniqueProds A] : IsLeftCancelMulZero (MonoidAlgebra R A) where
  mul_left_cancel_of_ne_zero {f g₁ g₂} hf eq := by
    classical
    set s := g₁.support ∪ g₂.support with hs
    clear_value s; revert g₁ g₂
    induction' s using Finset.eraseInduction with _ ih
    rintro g₁ g₂ eq rfl
    obtain h | h := (g₁.support ∪ g₂.support).eq_empty_or_nonempty
    · simp_rw [Finset.union_eq_empty, support_eq_empty] at h; exact h.1.trans h.2.symm
    have ⟨af, haf, ag, hag, uniq⟩ := UniqueProds.uniqueMul_of_nonempty (support_nonempty_iff.2 hf) h
    have := mul_apply_mul_eq_mul_of_uniqueMul_of_subset subset_rfl Finset.subset_union_left uniq
    rw [eq, mul_apply_mul_eq_mul_of_uniqueMul_of_subset subset_rfl Finset.subset_union_right uniq]
      at this
    have := mul_left_cancel₀ (mem_support_iff.mp haf) this
    rw [← g₁.erase_add_single ag, ← g₂.erase_add_single ag, this] at eq ⊢
    simp_rw [mul_add, add_right_cancel_iff] at eq
    rw [ih ag hag eq]
    simp_rw [support_erase, Finset.erase_union_distrib]

instance instIsRightCancelMulZeroOfUniqueProds [IsCancelAdd R] [IsRightCancelMulZero R] [Mul A]
    [UniqueProds A] : IsRightCancelMulZero (MonoidAlgebra R A) :=
  MulOpposite.isLeftCancelMulZero_iff.mp <|
    MonoidAlgebra.opRingEquiv.injective.isLeftCancelMulZero _ (map_zero _) (map_mul _)

instance instIsCancelMulZeroOfUniqueProds [IsCancelAdd R] [IsCancelMulZero R] [Mul A]
    [UniqueProds A] : IsCancelMulZero (MonoidAlgebra R A) where

instance instIsDomainOfUniqueProds [IsCancelAdd R] [IsDomain R] [Monoid A] [UniqueProds A] :
    IsDomain (MonoidAlgebra R A) where

end MonoidAlgebra

namespace AddMonoidAlgebra

theorem mul_apply_add_eq_mul_of_uniqueAdd_of_subset [Add A] {f g : AddMonoidAlgebra R A} {a0 b0 : A}
    {sf sg : Finset A} (hf : f.support ⊆ sf) (hg : g.support ⊆ sg) (h : UniqueAdd sf sg a0 b0) :
    (f * g) (a0 + b0) = f a0 * g b0 :=
  MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul_of_subset (A := Multiplicative A) hf hg h

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_uniqueAdd [Add A] {f g : R[A]} {a0 b0 : A}
    (h : UniqueAdd f.support g.support a0 b0) :
    (f * g) (a0 + b0) = f a0 * g b0 :=
  mul_apply_add_eq_mul_of_uniqueAdd_of_subset subset_rfl subset_rfl h

instance instNoZeroDivisorsOfUniqueSums [NoZeroDivisors R] [Add A] [UniqueSums A] :
    NoZeroDivisors R[A] := MonoidAlgebra.instNoZeroDivisorsOfUniqueProds (A := Multiplicative A)

instance instIsLeftCancelMulZeroOfUniqueSums [IsCancelAdd R] [IsLeftCancelMulZero R] [Add A]
    [UniqueSums A] : IsLeftCancelMulZero R[A] :=
  MonoidAlgebra.instIsLeftCancelMulZeroOfUniqueProds (A := Multiplicative A)

instance instIsRightCancelMulZeroOfUniqueSums [IsCancelAdd R] [IsRightCancelMulZero R] [Add A]
    [UniqueSums A] : IsRightCancelMulZero R[A] :=
  MonoidAlgebra.instIsRightCancelMulZeroOfUniqueProds (A := Multiplicative A)

instance instIsCancelMulZeroOfUniqueSums [IsCancelAdd R] [IsCancelMulZero R] [Add A]
    [UniqueSums A] : IsCancelMulZero R[A] where

instance instIsDomainOfUniqueSums [IsCancelAdd R] [IsDomain R] [AddMonoid A] [UniqueSums A] :
    IsDomain R[A] where

end AddMonoidAlgebra
end Semiring
