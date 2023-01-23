/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module data.set.intervals.infinite
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/


variable {α : Type _} [Preorder α]

/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.Injective
#align no_max_order.infinite NoMaxOrder.infinite

/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _
#align no_min_order.infinite NoMinOrder.infinite

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
#align set.Ioo.infinite Set.Ioo.infinite

theorem ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h
#align set.Ioo_infinite Set.ioo_infinite

theorem ico_infinite : (Ico a b).Infinite :=
  (ioo_infinite h).mono Ioo_subset_Ico_self
#align set.Ico_infinite Set.ico_infinite

theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| ico_infinite h
#align set.Ico.infinite Set.Ico.infinite

theorem ioc_infinite : (Ioc a b).Infinite :=
  (ioo_infinite h).mono Ioo_subset_Ioc_self
#align set.Ioc_infinite Set.ioc_infinite

theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| ioc_infinite h
#align set.Ioc.infinite Set.Ioc.infinite

theorem icc_infinite : (Icc a b).Infinite :=
  (ioo_infinite h).mono Ioo_subset_Icc_self
#align set.Icc_infinite Set.icc_infinite

theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| icc_infinite h
#align set.Icc.infinite Set.Icc.infinite

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite

theorem iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 Iio.infinite
#align set.Iio_infinite Set.iio_infinite

instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite

theorem iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 Iic.infinite
#align set.Iic_infinite Set.iic_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite

theorem ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 Ioi.infinite
#align set.Ioi_infinite Set.ioi_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite

theorem ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 Ici.infinite
#align set.Ici_infinite Set.ici_infinite

end Set

