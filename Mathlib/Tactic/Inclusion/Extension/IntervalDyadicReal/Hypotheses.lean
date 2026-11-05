/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
public import Mathlib.Data.Dyadic.Floor
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Init

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Hypothesis operations for dyadic real intervals

This file defines the hypothesis extensions for the `interval_dyadic_real` inclusion family.
-/

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_le {x y : ℝ} {I : Interval Dyadic} (hxy : x ≤ y) (hy : y ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_le hxy hy

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_le {x y : ℝ} {I : Interval Dyadic} (hxy : x ≤ y) (hx : x ∈ I) :
    y ∈ Interval.Ici I.lb := Interval.mem_Ici_of_le hxy hx

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_lt {x y : ℝ} {I : Interval Dyadic} (hxy : x < y) (hy : y ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_lt hxy hy

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_lt {x y : ℝ} {I : Interval Dyadic} (hxy : x < y) (hx : x ∈ I) :
    y ∈ Interval.Ici I.lb := Interval.mem_Ici_of_lt hxy hx

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_mem_Ici {a x : ℝ} {I : Interval Dyadic} (hx : x ∈ Set.Ici a) (ha : a ∈ I) :
    x ∈ Interval.Ici I.lb := Interval.mem_Ici_of_mem_Ici hx ha

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_mem_Ioi {a x : ℝ} {I : Interval Dyadic} (hx : x ∈ Set.Ioi a) (ha : a ∈ I) :
    x ∈ Interval.Ici I.lb := Interval.mem_Ici_of_mem_Ioi hx ha

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_mem_Iic {b x : ℝ} {I : Interval Dyadic} (hx : x ∈ Set.Iic b) (hb : b ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_mem_Iic hx hb

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_mem_Iio {b x : ℝ} {I : Interval Dyadic} (hx : x ∈ Set.Iio b) (hb : b ∈ I) :
    x ∈ Interval.Iic I.ub := Interval.mem_Iic_of_mem_Iio hx hb

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_mem_Ico {a b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ Set.Ico a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_mem_Ico hx ha hb

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_mem_Ioc {a b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ Set.Ioc a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_mem_Ioc hx ha hb

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_mem_Icc {a b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ Set.Icc a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_mem_Icc hx ha hb

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_mem_Ioo {a b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ Set.Ioo a b)
    (ha : a ∈ I) (hb : b ∈ J) : x ∈ Interval.Icc I.lb J.ub :=
  Interval.mem_Icc_of_mem_Ioo hx ha hb

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_intCast_le {z : ℤ} {y : ℝ} {I : Interval Dyadic}
    (hxy : (z : ℝ) ≤ y) (hy : y ∈ I) :
    z ∈ Interval.Iic (I.ub.map Dyadic.intFloor) := by
  refine ⟨bot_le, ?_⟩
  simpa [Interval.Iic, Interval.map, WithTop.map_map, Function.comp_def] using
    Int.floor_mono.withTop_map ((WithTop.coe_le_coe.mpr hxy).trans hy.2)

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_le_intCast {x : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hxy : x ≤ (z : ℝ)) (hx : x ∈ I) :
    z ∈ Interval.Ici (I.lb.map Dyadic.intCeil) := by
  refine ⟨?_, le_top⟩
  simpa [Interval.Ici, Interval.map, WithBot.map_map, Function.comp_def] using
    Int.ceil_mono.withBot_map (hx.1.trans (WithBot.coe_le_coe.mpr hxy))

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_intCast_lt {z : ℤ} {y : ℝ} {I : Interval Dyadic}
    (hxy : (z : ℝ) < y) (hy : y ∈ I) :
    z ∈ Interval.Iic (I.ub.map Dyadic.intCeil - 1) := by
  refine ⟨bot_le, ?_⟩
  grw [WithTop.coe_le_coe.mpr (Int.le_sub_one_of_lt (Int.lt_ceil.mpr hxy))]
  simpa [Interval.Iic, Interval.map, WithTop.map_map, Function.comp_def, sub_eq_add_neg] using
    add_le_add_right (Int.ceil_mono.withTop_map hy.2) (-1)

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_lt_intCast {x : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hxy : x < (z : ℝ)) (hx : x ∈ I) :
    z ∈ Interval.Ici (I.lb.map Dyadic.intFloor + 1) := by
  refine ⟨?_, le_top⟩
  grw [← WithBot.coe_le_coe.mpr (Int.add_one_le_of_lt (Int.floor_lt.mpr hxy))]
  simpa [Interval.Ici, Interval.map, WithBot.map_map, Function.comp_def, add_comm] using
    add_le_add_right (Int.floor_mono.withBot_map hx.1) 1

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_intCast_mem_Ici {a : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Ici a) (ha : a ∈ I) :
    z ∈ Interval.Ici (I.lb.map Dyadic.intCeil) := Ici_mem_of_le_intCast hz ha

@[hypothesis_op interval_dyadic_real]
theorem Ici_mem_of_intCast_mem_Ioi {a : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Ioi a) (ha : a ∈ I) :
    z ∈ Interval.Ici (I.lb.map Dyadic.intFloor + 1) := Ici_mem_of_lt_intCast hz ha

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_intCast_mem_Iic {b : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Iic b) (hb : b ∈ I) :
    z ∈ Interval.Iic (I.ub.map Dyadic.intFloor) := Iic_mem_of_intCast_le hz hb

@[hypothesis_op interval_dyadic_real]
theorem Iic_mem_of_intCast_mem_Iio {b : ℝ} {z : ℤ} {I : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Iio b) (hb : b ∈ I) :
    z ∈ Interval.Iic (I.ub.map Dyadic.intCeil - 1) := Iic_mem_of_intCast_lt hz hb

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_intCast_mem_Icc {a b : ℝ} {z : ℤ} {I J : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Icc a b) (ha : a ∈ I) (hb : b ∈ J) :
    z ∈ Interval.Icc (I.lb.map Dyadic.intCeil) (J.ub.map Dyadic.intFloor) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_le_intCast hz.1 ha) (Iic_mem_of_intCast_le hz.2 hb)

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_intCast_mem_Ico {a b : ℝ} {z : ℤ} {I J : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Ico a b) (ha : a ∈ I) (hb : b ∈ J) :
    z ∈ Interval.Icc (I.lb.map Dyadic.intCeil) (J.ub.map Dyadic.intCeil - 1) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_le_intCast hz.1 ha) (Iic_mem_of_intCast_lt hz.2 hb)

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_intCast_mem_Ioc {a b : ℝ} {z : ℤ} {I J : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Ioc a b) (ha : a ∈ I) (hb : b ∈ J) :
    z ∈ Interval.Icc (I.lb.map Dyadic.intFloor + 1) (J.ub.map Dyadic.intFloor) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_lt_intCast hz.1 ha) (Iic_mem_of_intCast_le hz.2 hb)

@[hypothesis_op interval_dyadic_real]
theorem Icc_mem_of_intCast_mem_Ioo {a b : ℝ} {z : ℤ} {I J : Interval Dyadic}
    (hz : (z : ℝ) ∈ Set.Ioo a b) (ha : a ∈ I) (hb : b ∈ J) :
    z ∈ Interval.Icc (I.lb.map Dyadic.intFloor + 1) (J.ub.map Dyadic.intCeil - 1) :=
  Interval.mem_Icc_of_mem (Ici_mem_of_lt_intCast hz.1 ha) (Iic_mem_of_intCast_lt hz.2 hb)

end IntervalDyadicReal

end Inclusion
