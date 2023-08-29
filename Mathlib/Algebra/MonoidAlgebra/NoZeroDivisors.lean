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

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
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
        · simp only [not_mem_support_iff.mp af, zero_mul, ite_self]
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
theorem NoZeroDivisors.of_left_ordered [NoZeroDivisors R] [AddRightCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (· + ·) (· < ·)] : NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨@fun f g fg => by
    contrapose! fg
    -- ⊢ f * g ≠ 0
    let gmin : A := g.support.min' (support_nonempty_iff.mpr fg.2)
    -- ⊢ f * g ≠ 0
    refine' support_nonempty_iff.mp _
    -- ⊢ Finset.Nonempty (f * g).support
    obtain ⟨a, ha, H⟩ :=
      Right.exists_add_of_mem_support_single_mul gmin
        ((f * single gmin 1 : AddMonoidAlgebra R A).support.min'
          (by rw [support_mul_single] <;> simp [support_nonempty_iff.mpr fg.1]))
        (Finset.min'_mem _ _)
    refine' ⟨a + gmin, mem_support_iff.mpr _⟩
    -- ⊢ ↑(f * g) (a + gmin) ≠ 0
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    -- ⊢ ↑f a * ↑g gmin ≠ 0
    · refine' mul_ne_zero _ _
      -- ⊢ ↑f a ≠ 0
      exacts [mem_support_iff.mp ha, mem_support_iff.mp (Finset.min'_mem _ _)]
      -- 🎉 no goals
    · rw [H]
      -- ⊢ ∀ {a_1 b : A}, a_1 ∈ f.support → b ∈ g.support → a_1 ≠ a ∨ b ≠ gmin → a_1 +  …
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      -- ⊢ b + c ≠ Finset.min' (f * single gmin 1).support (_ : Finset.Nonempty (f * si …
                                     -- ⊢ Finset.min' (f * single gmin 1).support (_ : Finset.Nonempty (f * single gmi …
                                     -- ⊢ Finset.min' (f * single gmin 1).support (_ : Finset.Nonempty (f * single gmi …
      · refine' lt_of_lt_of_le (_ : _ < b + gmin) _
        -- ⊢ Finset.min' (f * single gmin 1).support (_ : Finset.Nonempty (f * single gmi …
        · apply Finset.min'_lt_of_mem_erase_min'
          -- ⊢ b + gmin ∈ Finset.erase (f * single gmin 1).support (Finset.min' (f * single …
          rw [← H]
          -- ⊢ b + gmin ∈ Finset.erase (f * single gmin 1).support (a + gmin)
          apply Finset.mem_erase_of_ne_of_mem
          -- ⊢ b + gmin ≠ a + gmin
          · simpa only [Ne.def, add_left_inj]
            -- 🎉 no goals
          · rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
            -- ⊢ b + gmin ∈ Finset.map (addRightEmbedding gmin) f.support
            simpa only [Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (· + ·) (· ≤ ·) := Add.to_covariantClass_left A
          -- ⊢ b + gmin ≤ b + c
          exact add_le_add_left (Finset.min'_le _ _ cg) _
          -- 🎉 no goals
      · refine' lt_of_le_of_lt (_ : _ ≤ b + gmin) _
        -- ⊢ Finset.min' (f * single gmin 1).support (_ : Finset.Nonempty (f * single gmi …
        · apply Finset.min'_le
          -- ⊢ b + gmin ∈ (f * single gmin 1).support
          rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
          -- ⊢ b + gmin ∈ Finset.map (addRightEmbedding gmin) f.support
          simp only [bf, Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_left _ _
          -- ⊢ gmin < c
          exact Finset.min'_lt_of_mem_erase_min' _ _ (Finset.mem_erase.mpr ⟨hc, cg⟩)⟩
          -- 🎉 no goals
#align add_monoid_algebra.no_zero_divisors.of_left_ordered AddMonoidAlgebra.NoZeroDivisors.of_left_ordered

/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a right-ordered add left
cancel semigroup, then `AddMonoidAlgebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_right_ordered [NoZeroDivisors R] [AddLeftCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (Function.swap (· + ·)) (· < ·)] :
    NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨@fun f g fg => by
    contrapose! fg
    -- ⊢ f * g ≠ 0
    let fmin : A := f.support.min' (support_nonempty_iff.mpr fg.1)
    -- ⊢ f * g ≠ 0
    refine' support_nonempty_iff.mp _
    -- ⊢ Finset.Nonempty (f * g).support
    obtain ⟨a, ha, H⟩ :=
      Left.exists_add_of_mem_support_single_mul fmin
        ((single fmin 1 * g : AddMonoidAlgebra R A).support.min'
          (by rw [support_single_mul] <;> simp [support_nonempty_iff.mpr fg.2]))
        (Finset.min'_mem _ _)
    refine' ⟨fmin + a, mem_support_iff.mpr _⟩
    -- ⊢ ↑(f * g) (fmin + a) ≠ 0
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    -- ⊢ ↑f fmin * ↑g a ≠ 0
    · refine' mul_ne_zero _ _
      -- ⊢ ↑f fmin ≠ 0
      exacts [mem_support_iff.mp (Finset.min'_mem _ _), mem_support_iff.mp ha]
      -- 🎉 no goals
    · rw [H]
      -- ⊢ ∀ {a_1 b : A}, a_1 ∈ f.support → b ∈ g.support → a_1 ≠ fmin ∨ b ≠ a → a_1 +  …
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      -- ⊢ b + c ≠ Finset.min' (single fmin 1 * g).support (_ : Finset.Nonempty (single …
                                     -- ⊢ Finset.min' (single fmin 1 * g).support (_ : Finset.Nonempty (single fmin 1  …
                                     -- ⊢ Finset.min' (single fmin 1 * g).support (_ : Finset.Nonempty (single fmin 1  …
      · refine' lt_of_le_of_lt (_ : _ ≤ fmin + c) _
        -- ⊢ Finset.min' (single fmin 1 * g).support (_ : Finset.Nonempty (single fmin 1  …
        · apply Finset.min'_le
          -- ⊢ fmin + c ∈ (single fmin 1 * g).support
          rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
          -- ⊢ fmin + c ∈ Finset.map (addLeftEmbedding fmin) g.support
          simp only [cg, Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_right _ _
          -- ⊢ fmin < b
          exact Finset.min'_lt_of_mem_erase_min' _ _ (Finset.mem_erase.mpr ⟨hb, bf⟩)
          -- 🎉 no goals
      · refine' lt_of_lt_of_le (_ : _ < fmin + c) _
        -- ⊢ Finset.min' (single fmin 1 * g).support (_ : Finset.Nonempty (single fmin 1  …
        · apply Finset.min'_lt_of_mem_erase_min'
          -- ⊢ fmin + c ∈ Finset.erase (single fmin 1 * g).support (Finset.min' (single fmi …
          rw [← H]
          -- ⊢ fmin + c ∈ Finset.erase (single fmin 1 * g).support (fmin + a)
          apply Finset.mem_erase_of_ne_of_mem
          -- ⊢ fmin + c ≠ fmin + a
          · simpa only [Ne.def, add_right_inj]
            -- 🎉 no goals
          · rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
            -- ⊢ fmin + c ∈ Finset.map (addLeftEmbedding fmin) g.support
            simpa only [Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (Function.swap (· + ·)) (· ≤ ·) :=
            Add.to_covariantClass_right A
          exact add_le_add_right (Finset.min'_le _ _ bf) _⟩
          -- 🎉 no goals
#align add_monoid_algebra.no_zero_divisors.of_right_ordered AddMonoidAlgebra.NoZeroDivisors.of_right_ordered

end LeftOrRightOrderability

end AddMonoidAlgebra
