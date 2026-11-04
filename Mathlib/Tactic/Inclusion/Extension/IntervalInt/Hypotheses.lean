/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Init

/-!
# Hypothesis operations for integer intervals

This file defines the hypothesis extensions for `interval_int`.
-/

@[expose] public section

namespace Inclusion.IntervalInt

@[hypothesis_op interval_int]
theorem Iic_mem_of_le {x y : ℤ} {I : Interval ℤ} (hxy : x ≤ y) (hy : y ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_le hxy hy

@[hypothesis_op interval_int]
theorem Ici_mem_of_le {x y : ℤ} {I : Interval ℤ} (hxy : x ≤ y) (hx : x ∈ I) :
    y ∈ Interval.Ici I.lb := Interval.mem_Ici_of_le hxy hx

@[hypothesis_op interval_int]
theorem Iic_mem_of_lt {x y : ℤ} {I : Interval ℤ} (hxy : x < y) (hy : y ∈ I) :
    x ∈ Interval.Iic (I.ub - 1) := by
  refine ⟨bot_le, ?_⟩
  grw [WithTop.coe_le_coe.mpr (Int.le_sub_one_of_lt hxy)]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top WithTop.coe_ne_top).mpr hy.2

@[hypothesis_op interval_int]
theorem Ici_mem_of_lt {x y : ℤ} {I : Interval ℤ} (hxy : x < y) (hx : x ∈ I) :
    y ∈ Interval.Ici (I.lb + 1) := by
  refine ⟨?_, le_top⟩
  grw [← WithBot.coe_le_coe.mpr (Int.add_one_le_of_lt hxy)]
  exact add_le_add_left hx.1 1

@[hypothesis_op interval_int]
theorem Ici_mem_of_mem_Ici {a x : ℤ} {I : Interval ℤ} (hx : x ∈ Set.Ici a) (ha : a ∈ I) :
    x ∈ Interval.Ici I.lb := Interval.mem_Ici_of_mem_Ici hx ha

@[hypothesis_op interval_int]
theorem Ici_mem_of_mem_Ioi {a x : ℤ} {I : Interval ℤ} (hx : x ∈ Set.Ioi a) (ha : a ∈ I) :
    x ∈ Interval.Ici (I.lb + 1) := Ici_mem_of_lt hx ha

@[hypothesis_op interval_int]
theorem Iic_mem_of_mem_Iic {b x : ℤ} {I : Interval ℤ} (hx : x ∈ Set.Iic b) (hb : b ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_mem_Iic hx hb

@[hypothesis_op interval_int]
theorem Iic_mem_of_mem_Iio {b x : ℤ} {I : Interval ℤ} (hx : x ∈ Set.Iio b) (hb : b ∈ I) :
    x ∈ Interval.Iic (I.ub - 1) := Iic_mem_of_lt hx hb

@[hypothesis_op interval_int]
theorem Icc_mem_of_mem_Icc {a b x : ℤ} {I J : Interval ℤ} (hx : x ∈ Set.Icc a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_mem_Icc hx ha hb

@[hypothesis_op interval_int]
theorem Icc_mem_of_mem_Ico {a b x : ℤ} {I J : Interval ℤ} (hx : x ∈ Set.Ico a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb (J.ub - 1) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_le hx.1 ha) (Iic_mem_of_lt hx.2 hb)

@[hypothesis_op interval_int]
theorem Icc_mem_of_mem_Ioc {a b x : ℤ} {I J : Interval ℤ} (hx : x ∈ Set.Ioc a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc (I.lb + 1) J.ub :=
  Interval.mem_Icc_of_mem (Ici_mem_of_lt hx.1 ha) (Iic_mem_of_le hx.2 hb)

@[hypothesis_op interval_int]
theorem Icc_mem_of_mem_Ioo {a b x : ℤ} {I J : Interval ℤ} (hx : x ∈ Set.Ioo a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc (I.lb + 1) (J.ub - 1) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_lt hx.1 ha) (Iic_mem_of_lt hx.2 hb)

end Inclusion.IntervalInt
