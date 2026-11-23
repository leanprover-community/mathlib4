/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs

import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! # Pointwise operations on intervals

This should be kept in sync with `Mathlib/Algebra/Order/Group/Pointwise/Interval.lean`.
-/

public section

variable {α : Type*}

namespace Finset

open scoped Pointwise

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Finset.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [DecidableEq α]
variable [MulLeftMono α] [MulRightMono α]

@[to_additive]
theorem Icc_mul_Icc_subset [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d ⊆ Icc (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Icc_subset _ _ _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Icc_add_Icc_subset]
alias Icc_mul_Icc_subset' := Finset.Icc_mul_Icc_subset

@[to_additive]
theorem Iic_mul_Iic_subset [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b ⊆ Iic (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iic_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Iic_add_Iic_subset]
alias Iic_mul_Iic_subset' := Finset.Iic_mul_Iic_subset

@[to_additive]
theorem Ici_mul_Ici_subset [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b ⊆ Ici (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ici_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ici_add_Ici_subset]
alias Ici_mul_Ici_subset' := Finset.Ici_mul_Ici_subset

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [DecidableEq α]
variable [MulLeftStrictMono α] [MulRightStrictMono α]

@[to_additive]
theorem Icc_mul_Ico_subset [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Ico_subset _ _ _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Icc_add_Ico_subset]
alias Icc_mul_Ico_subset' := Finset.Icc_mul_Ico_subset

@[to_additive]
theorem Ico_mul_Icc_subset [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Icc c d ⊆ Ico (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Icc_subset _ _ _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ico_add_Icc_subset]
alias Ico_mul_Icc_subset' := Finset.Ico_mul_Icc_subset

@[to_additive]
theorem Ioc_mul_Ico_subset [LocallyFiniteOrder α] (a b c d : α) :
    Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioc_mul_Ico_subset _ _ _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ioc_add_Ico_subset]
alias Ioc_mul_Ico_subset' := Finset.Ioc_mul_Ico_subset

@[to_additive]
theorem Ico_mul_Ioc_subset [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) :=
  Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Ioc_subset _ _ _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ico_add_Ioc_subset]
alias Ico_mul_Ioc_subset' := Finset.Ico_mul_Ioc_subset

@[to_additive]
theorem Iic_mul_Iio_subset [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iio_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Iic_add_Iio_subset]
alias Iic_mul_Iio_subset' := Finset.Iic_mul_Iio_subset

@[to_additive]
theorem Iio_mul_Iic_subset [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b ⊆ Iio (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Iio_mul_Iic_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Iio_add_Iic_subset]
alias Iio_mul_Iic_subset' := Finset.Iio_mul_Iic_subset

@[to_additive]
theorem Ioi_mul_Ici_subset [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ioi_mul_Ici_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ioi_add_Ici_subset]
alias Ioi_mul_Ici_subset' := Finset.Ioi_mul_Ici_subset

@[to_additive]
theorem Ici_mul_Ioi_subset [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) :=
  Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ioi_subset _ _

@[deprecated (since := "2026-11-22"), to_additive existing _root_.Finset.Ici_add_Ioi_subset]
alias Ici_mul_Ioi_subset' := Finset.Ici_mul_Ioi_subset

end ContravariantLT

end Finset
