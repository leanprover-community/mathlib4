/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Support

#align_import algebra.monoid_algebra.no_zero_divisors from "leanprover-community/mathlib"@"3e067975886cf5801e597925328c335609511b1a"

/-!
# Variations on non-zero divisors in `AddMonoidAlgebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `AddMonoidAlgebra R A` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

We formalize in this file the well-known result that if `R` is a field and `A` is a left-ordered
group, then `R[A]` contains no non-zero zero-divisors.  Some of these assumptions can be trivially
weakened: below we mention what assumptions are sufficient for the proofs in this file.

##  Main results

* `NoZeroDivisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `AddMonoidAlgebra R A` has no non-zero zero-divisors.
* `NoZeroDivisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `AddMonoidAlgebra R A` has no non-zero zero-divisors.

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


namespace AddMonoidAlgebra

open Finsupp

variable {R A : Type*} [Semiring R]

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_forall_ne [Add A] {f g : AddMonoidAlgebra R A} {a0 b0 : A}
    (h : ∀ {a b : A}, a ∈ f.support → b ∈ g.support → a ≠ a0 ∨ b ≠ b0 → a + b ≠ a0 + b0) :
    (f * g) (a0 + b0) = f a0 * g b0 := by
  classical
    rw [mul_apply]
    refine' (Finset.sum_eq_single a0 _ _).trans _
    · exact fun b H hb => Finset.sum_eq_zero fun x H1 => if_neg (h H H1 (Or.inl hb))
    · exact fun af0 => by simp [not_mem_support_iff.mp af0]
    · refine' (Finset.sum_eq_single b0 (fun b bg b0 => _) _).trans (if_pos rfl)
      · by_cases af : a0 ∈ f.support
        · exact if_neg (h af bg (Or.inr b0))
        · simp only [not_mem_support_iff.mp af, MulZeroClass.zero_mul, ite_self]
      · exact fun bf0 => by simp [not_mem_support_iff.mp bf0]
#align add_monoid_algebra.mul_apply_add_eq_mul_of_forall_ne AddMonoidAlgebra.mul_apply_add_eq_mul_of_forall_ne

section LeftOrRightOrderability

theorem Left.exists_add_of_mem_support_single_mul [AddLeftCancelSemigroup A]
    {g : AddMonoidAlgebra R A} (a x : A)
    (hx : x ∈ (single a 1 * g : AddMonoidAlgebra R A).support) : ∃ b ∈ g.support, a + b = x := by
  rwa [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _),
    Finset.mem_map] at hx
#align add_monoid_algebra.left.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Left.exists_add_of_mem_support_single_mul

theorem Right.exists_add_of_mem_support_single_mul [AddRightCancelSemigroup A]
    {f : AddMonoidAlgebra R A} (b x : A)
    (hx : x ∈ (f * single b 1 : AddMonoidAlgebra R A).support) : ∃ a ∈ f.support, a + b = x := by
  rwa [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _),
    Finset.mem_map] at hx
#align add_monoid_algebra.right.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Right.exists_add_of_mem_support_single_mul

/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a left-ordered add right
cancel semigroup, then `AddMonoidAlgebra R A` also contains no non-zero zero-divisors. -/
instance NoZeroDivisors.of_left_ordered [NoZeroDivisors R] [AddRightCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (· + ·) (· < ·)] : NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨@fun f g fg => by
    contrapose! fg
    let gmin : A := g.support.min' (support_nonempty_iff.mpr fg.2)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      Right.exists_add_of_mem_support_single_mul gmin
        ((f * single gmin 1 : AddMonoidAlgebra R A).support.min'
          (by rw [support_mul_single] <;> simp [support_nonempty_iff.mpr fg.1]))
        (Finset.min'_mem _ _)
    refine' ⟨a + gmin, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts [mem_support_iff.mp ha, mem_support_iff.mp (Finset.min'_mem _ _)]
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      · refine' lt_of_lt_of_le (_ : _ < b + gmin) _
        · apply Finset.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finset.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_left_inj]
          · rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
            simpa only [Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (· + ·) (· ≤ ·) := Add.to_covariantClass_left A
          exact add_le_add_left (Finset.min'_le _ _ cg) _
      · refine' lt_of_le_of_lt (_ : _ ≤ b + gmin) _
        · apply Finset.min'_le
          rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
          simp only [bf, Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_left _ _
          exact Finset.min'_lt_of_mem_erase_min' _ _ (Finset.mem_erase.mpr ⟨hc, cg⟩)⟩
#align add_monoid_algebra.no_zero_divisors.of_left_ordered AddMonoidAlgebra.NoZeroDivisors.of_left_ordered

/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a right-ordered add left
cancel semigroup, then `AddMonoidAlgebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_right_ordered [NoZeroDivisors R] [AddLeftCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (Function.swap (· + ·)) (· < ·)] :
    NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨@fun f g fg => by
    contrapose! fg
    let fmin : A := f.support.min' (support_nonempty_iff.mpr fg.1)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      Left.exists_add_of_mem_support_single_mul fmin
        ((single fmin 1 * g : AddMonoidAlgebra R A).support.min'
          (by rw [support_single_mul] <;> simp [support_nonempty_iff.mpr fg.2]))
        (Finset.min'_mem _ _)
    refine' ⟨fmin + a, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts [mem_support_iff.mp (Finset.min'_mem _ _), mem_support_iff.mp ha]
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      · refine' lt_of_le_of_lt (_ : _ ≤ fmin + c) _
        · apply Finset.min'_le
          rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
          simp only [cg, Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_right _ _
          exact Finset.min'_lt_of_mem_erase_min' _ _ (Finset.mem_erase.mpr ⟨hb, bf⟩)
      · refine' lt_of_lt_of_le (_ : _ < fmin + c) _
        · apply Finset.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finset.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_right_inj]
          · rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
            simpa only [Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (Function.swap (· + ·)) (· ≤ ·) :=
            Add.to_covariantClass_right A
          exact add_le_add_right (Finset.min'_le _ _ bf) _⟩
#align add_monoid_algebra.no_zero_divisors.of_right_ordered AddMonoidAlgebra.NoZeroDivisors.of_right_ordered

end LeftOrRightOrderability

set_option autoImplicit false

section Covariant_lt
variable [Add A]

section PartialOrder
variable [PartialOrder A] [CovariantClass A A (· + ·) (· < ·)] {a t b : A}
  {f g : AddMonoidAlgebra R A}

/--  The "top" element of `AddMonoidAlgebra.single a r * f` is the product of `r` and
the "top" element of `f`.  Here, "top" is simply an upper bound for the elements
of the support of `f` (e.g. the product is `0` if "top" is not a maximum).
The corresponding statement for a general product `f * g` is `AddMonoidAlgebra.mul_apply_of_le`.
It is proved with a further `CovariantClass` assumption. -/
theorem single_mul_apply_of_le (r : R) (ft : ∀ a ∈ f.support, a ≤ t) :
  ((AddMonoidAlgebra.single a r) * f) (a + t) = r * f t := by
  classical
  simp only [id_eq]
  nth_rw 1 [← f.erase_add_single t]
  rw [mul_add, single_mul_single, Finsupp.add_apply, Finsupp.single_eq_same]
  convert zero_add _
  refine Finsupp.not_mem_support_iff.mp (fun h ↦ ?_)
  refine not_not.mpr ((support_mul (Finsupp.single a r) (f.erase t)) h) ?_
  simp only [Finsupp.mem_support_single, Finset.mem_biUnion, Ne.def, Finset.mem_singleton,
    exists_prop, not_exists, not_and, and_imp, forall_eq, Finsupp.support_erase]
  intros _ x xs
  refine (add_lt_add_left (WithBot.coe_lt_coe.mp ?_) _).ne'
  refine WithBot.coe_lt_coe.mpr ((ft _ (Finset.mem_of_mem_erase xs)).lt_of_ne ?_)
  exact Finset.ne_of_mem_erase xs

/--  The "bottom" element of `Finsupp.single a r * f` is the product of `r` and
the "bottom" element of `f`.  Here, "bottom" is simply a lower bound for the elements
of the support of `f` (e.g. the product is `0` if "bottom" is not a minimum).
The corresponding statement for a general product `f * g` is `AddMonoidAlgebra.mul_apply_of_le'`.
It is proved with a further `CovariantClass` assumption. -/
theorem single_mul_apply_of_le' (r : R) (fb : ∀ a ∈ f.support, b ≤ a) :
  ((AddMonoidAlgebra.single a r) * f) (a + b) = r * f b :=
@single_mul_apply_of_le _ Aᵒᵈ _ _ _ _ _ _ _ _ fb

variable [CovariantClass A A (Function.swap (· + ·)) (· < ·)]

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
  simp only [Finsupp.support_erase, Finset.mem_biUnion, Finset.mem_erase, Ne.def,
    Finset.mem_singleton, exists_prop, not_exists, not_and, and_imp]
  haveI : CovariantClass A A (· + ·) (· ≤ ·) := Add.to_covariantClass_left A
  exact fun x xa xf y yg ↦ (add_lt_add_of_lt_of_le ((fa _ xf).lt_of_ne xa) (gt _ yg)).ne'

/--  The "bottom" element of `f * g` is the product of the "bottom" elements of `f` and of `g`.
Here, "bottom" is simply a lower bound for the elements of the support of the corresponding
polynomial (e.g. the product is `0` if "bottom" is not a minimum). -/
theorem mul_apply_of_le' (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b ≤ i) :
  (f * g) (a + b) = f a * g b :=
@mul_apply_of_le _ Aᵒᵈ _ _ _ _ _ _ _ _ _ fa gb

theorem mul_apply_eq_zero_of_lt (fa : ∀ i ∈ f.support, a ≤ i) (gb : ∀ i ∈ g.support, b < i) :
  (f * g) (a + b) = 0 := by
  rw [mul_apply_of_le' fa (fun x hx ↦ ((gb _ hx).le))]
  convert mul_zero _
  exact Finsupp.not_mem_support_iff.mp (fun bg ↦ (lt_irrefl b (gb b bg)).elim)

end PartialOrder

section LinearOrder
variable [NoZeroDivisors R] [Add A] [LinearOrder A] [CovariantClass A A (· + ·) (· < ·)]
  [CovariantClass A A (Function.swap (· + ·)) (· < ·)]

protected theorem NoZeroDivisors.biOrdered : NoZeroDivisors (AddMonoidAlgebra R A) := ⟨by
  intros f g fg
  contrapose! fg
  apply_fun (fun x ↦ x (f.support.max' (Finsupp.support_nonempty_iff.mpr fg.1)
    + g.support.max' (Finsupp.support_nonempty_iff.mpr fg.2)))
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [mul_apply_of_le] <;>
    try exact Finset.le_max' _
  refine mul_ne_zero_iff.mpr ⟨?_, ?_⟩ <;>
    exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)⟩

end LinearOrder

end Covariant_lt

end AddMonoidAlgebra
