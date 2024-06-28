/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Nonneg.Order
import Mathlib.Algebra.Order.Nonneg.Ring

#align_import algebra.order.nonneg.ring from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

/-!
# Canonically ordered instances on nonnegative elements

## Main declarations

* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedAddCommMonoid` if `α` is a `LinearOrderedRing`.
* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedSemifield` if `α` is a `LinearOrderedField`.

-/

open Set

variable {α : Type*}

namespace Nonneg

instance canonicallyOrderedAddCommMonoid [OrderedRing α] :
    CanonicallyOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  { Nonneg.orderedAddCommMonoid, Nonneg.orderBot with
    le_self_add := fun _ b => le_add_of_nonneg_right b.2
    exists_add_of_le := fun {a b} h =>
      ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩ }
#align nonneg.canonically_ordered_add_monoid Nonneg.canonicallyOrderedAddCommMonoid

instance canonicallyOrderedCommSemiring [OrderedCommRing α] [NoZeroDivisors α] :
    CanonicallyOrderedCommSemiring { x : α // 0 ≤ x } :=
  { Nonneg.canonicallyOrderedAddCommMonoid, Nonneg.orderedCommSemiring with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self]}
#align nonneg.canonically_ordered_comm_semiring Nonneg.canonicallyOrderedCommSemiring

instance canonicallyLinearOrderedAddCommMonoid [LinearOrderedRing α] :
    CanonicallyLinearOrderedAddCommMonoid { x : α // 0 ≤ x } :=
  { Subtype.instLinearOrder _, Nonneg.canonicallyOrderedAddCommMonoid with }
#align nonneg.canonically_linear_ordered_add_monoid Nonneg.canonicallyLinearOrderedAddCommMonoid

end Nonneg
