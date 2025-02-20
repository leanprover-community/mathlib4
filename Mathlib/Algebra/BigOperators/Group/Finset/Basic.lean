/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Monoid.Finset.Basic
/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `Finset`).

## Notation

We introduce the following notation.

Let `s` be a `Finset α`, and `f : α → β` a function.

* `∏ x ∈ s, f x` is notation for `Finset.prod s f` (assuming `β` is a `CommMonoid`)
* `∑ x ∈ s, f x` is notation for `Finset.sum s f` (assuming `β` is an `AddCommMonoid`)
* `∏ x, f x` is notation for `Finset.prod Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is a `CommMonoid`)
* `∑ x, f x` is notation for `Finset.sum Finset.univ f`
  (assuming `α` is a `Fintype` and `β` is an `AddCommMonoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

-- TODO
-- assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction OrderedCommMonoid

variable {ι κ α β γ : Type*}

open Fin Function

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

end Finset



variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive]
theorem prod_insert_div {M : Type*} [CommGroup M] [DecidableEq α] (ha : a ∉ s) {f : α → M} :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by simp [ha]


end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

end

namespace Finset

section CommMonoid

variable [CommMonoid β]


variable (f s)


variable {f s}


section indicator
open Set
variable {κ : Type*}


end indicator


@[to_additive]
theorem prod_range_add_div_prod_range {α : Type*} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    (∏ k ∈ range (n + m), f k) / ∏ k ∈ range n, f k = ∏ k ∈ Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

open Multiset

/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued
function reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp

@[to_additive]
theorem prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by apply prod_range_induction <;> simp

@[to_additive]
theorem eq_prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel]

@[to_additive]
theorem eq_prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i ∈ range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid α] {s t : Finset ι} {f : ι → α}

end CancelCommMonoid

section CommGroup

variable [CommGroup β] [DecidableEq α]

@[to_additive (attr := simp)]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) :
    ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

@[to_additive (attr := simp)]
theorem prod_erase_eq_div {a : α} (h : a ∈ s) :
    ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

end CommGroup

section Image_Overlap

variable {α β ι : Type*} [DecidableEq α]

end Image_Overlap

end Finset

namespace Fintype
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid α]


variable [DecidableEq ι]

end CommMonoid
end Fintype

namespace List

end List

namespace Multiset


variable [DecidableEq α]

end Multiset


set_option linter.style.longFile 1800
