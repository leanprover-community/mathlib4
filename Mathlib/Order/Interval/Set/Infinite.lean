/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.Data.Set.Finite

#align_import data.set.intervals.infinite from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/


variable {α : Type*} [Preorder α]

/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `Infinite α → Nontrivial α → Nonempty α`. -/
theorem NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.injective
#align no_max_order.infinite NoMaxOrder.infinite

/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `Infinite α → Nontrivial α → Nonempty α`. -/
theorem NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _
#align no_min_order.infinite NoMinOrder.infinite

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
#align set.Ioo.infinite Set.Ioo.infinite

theorem Ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h
#align set.Ioo_infinite Set.Ioo_infinite

theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self
#align set.Ico_infinite Set.Ico_infinite

theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h
#align set.Ico.infinite Set.Ico.infinite

theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self
#align set.Ioc_infinite Set.Ioc_infinite

theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h
#align set.Ioc.infinite Set.Ioc.infinite

theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self
#align set.Icc_infinite Set.Icc_infinite

theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h
#align set.Icc.infinite Set.Icc.infinite

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite

theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 inferInstance
#align set.Iio_infinite Set.Iio_infinite

instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite

theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 inferInstance
#align set.Iic_infinite Set.Iic_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite

theorem Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 inferInstance
#align set.Ioi_infinite Set.Ioi_infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite

theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 inferInstance
#align set.Ici_infinite Set.Ici_infinite

end Set
