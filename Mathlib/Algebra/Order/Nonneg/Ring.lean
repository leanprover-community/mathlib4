/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Lattice
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Tactic.FastInstance

/-!
# Bundled ordered algebra instance on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `CanonicallyLinearOrderedAddCommMonoid` if `α` is a `LinearOrderedRing`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

open Set

variable {α : Type*}

namespace Nonneg

instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.isOrderedAddMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

instance isOrderedCancelAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid { x : α // 0 ≤ x } :=
  Subtype.coe_injective.isOrderedCancelAddMonoid _ Nonneg.coe_zero (fun _ _ => rfl) fun _ _ => rfl

instance isOrderedRing [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    IsOrderedRing { x : α // 0 ≤ x } :=
  Subtype.coe_injective.isOrderedRing _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _=> rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

instance isStrictOrderedRing [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    IsStrictOrderedRing { x : α // 0 ≤ x } :=
  Subtype.coe_injective.isStrictOrderedRing _ Nonneg.coe_zero Nonneg.coe_one
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance existsAddOfLE [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] :
    ExistsAddOfLE { x : α // 0 ≤ x } :=
  ⟨fun {a b} h ↦ by
    rw [← Subtype.coe_le_coe] at h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨⟨c, ?_⟩, by simp [Subtype.ext_iff, hc]⟩
    rw [← add_zero a.val, hc] at h
    exact le_of_add_le_add_left h⟩

instance nontrivial [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩

instance linearOrderedCommMonoidWithZero [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } :=
  { Nonneg.commSemiring, Nonneg.isOrderedRing with
    mul_le_mul_left := fun _ _ h c ↦ mul_le_mul_of_nonneg_left h c.prop }

instance canonicallyOrderedAdd [Ring α] [PartialOrder α] [IsOrderedRing α] :
    CanonicallyOrderedAdd { x : α // 0 ≤ x } where
  le_add_self _ b := le_add_of_nonneg_left b.2
  le_self_add _ b := le_add_of_nonneg_right b.2
  exists_add_of_le := fun {a b} h =>
    ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩

instance noZeroDivisors [Semiring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivisors α] :
    NoZeroDivisors { x : α // 0 ≤ x } :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self]}

instance orderedSub [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    OrderedSub { x : α // 0 ≤ x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le]⟩

end Nonneg
