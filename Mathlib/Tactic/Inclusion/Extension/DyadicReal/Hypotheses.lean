/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Basic

/-!
# Hypothesis operations for dyadic real intervals
-/

@[expose] public section

namespace Inclusion

private theorem mem_bounds {a b x : ℝ} {I J : Interval Dyadic}
    (ha : a ∈ I) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ∈ J) :
    x ∈ (⟨I.lb, J.ub⟩ : Interval Dyadic) :=
  ⟨ha.1.trans (WithBot.coe_le_coe.mpr hax),
    (WithTop.coe_le_coe.mpr hxb).trans hb.2⟩

@[hypothesisOp real.dyadic]
theorem downwardClosure_mem {x y : ℝ} {I : Interval Dyadic}
    (hxy : x ≤ y) (hy : y ∈ I) : x ∈ I.downwardClosure :=
  ⟨by simp [Interval.downwardClosure, Interval.map],
    (WithTop.coe_le_coe.mpr hxy).trans hy.2⟩

@[hypothesisOp real.dyadic]
theorem upwardClosure_mem {x y : ℝ} {I : Interval Dyadic}
    (hxy : x ≤ y) (hx : x ∈ I) : y ∈ I.upwardClosure :=
  ⟨hx.1.trans (WithBot.coe_le_coe.mpr hxy),
    by simp [Interval.upwardClosure, Interval.map]⟩

@[hypothesisOp real.dyadic]
theorem downwardClosure_mem_of_lt {x y : ℝ} {I : Interval Dyadic}
    (hxy : x < y) (hy : y ∈ I) : x ∈ I.downwardClosure :=
  downwardClosure_mem hxy.le hy

@[hypothesisOp real.dyadic]
theorem upwardClosure_mem_of_lt {x y : ℝ} {I : Interval Dyadic}
    (hxy : x < y) (hx : x ∈ I) : y ∈ I.upwardClosure :=
  upwardClosure_mem hxy.le hx

@[hypothesisOp real.dyadic]
theorem upwardClosure_mem_of_mem_Ici {a x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ Set.Ici a) (ha : a ∈ I) : x ∈ I.upwardClosure :=
  upwardClosure_mem (Set.mem_Ici.mp hx) ha

@[hypothesisOp real.dyadic]
theorem upwardClosure_mem_of_mem_Ioi {a x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ Set.Ioi a) (ha : a ∈ I) : x ∈ I.upwardClosure :=
  upwardClosure_mem (Set.mem_Ioi.mp hx).le ha

@[hypothesisOp real.dyadic]
theorem downwardClosure_mem_of_mem_Iic {b x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ Set.Iic b) (hb : b ∈ I) : x ∈ I.downwardClosure :=
  downwardClosure_mem (Set.mem_Iic.mp hx) hb

@[hypothesisOp real.dyadic]
theorem downwardClosure_mem_of_mem_Iio {b x : ℝ} {I : Interval Dyadic}
    (hx : x ∈ Set.Iio b) (hb : b ∈ I) : x ∈ I.downwardClosure :=
  downwardClosure_mem (Set.mem_Iio.mp hx).le hb

@[hypothesisOp real.dyadic]
theorem bounds_mem_of_mem_Ico {a b x : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ Set.Ico a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ (⟨I.lb, J.ub⟩ : Interval Dyadic) :=
  mem_bounds ha hx.1 hx.2.le hb

@[hypothesisOp real.dyadic]
theorem bounds_mem_of_mem_Ioc {a b x : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ Set.Ioc a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ (⟨I.lb, J.ub⟩ : Interval Dyadic) :=
  mem_bounds ha hx.1.le hx.2 hb

@[hypothesisOp real.dyadic]
theorem bounds_mem_of_mem_Icc {a b x : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ Set.Icc a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ (⟨I.lb, J.ub⟩ : Interval Dyadic) :=
  mem_bounds ha hx.1 hx.2 hb

@[hypothesisOp real.dyadic]
theorem bounds_mem_of_mem_Ioo {a b x : ℝ} {I J : Interval Dyadic}
    (hx : x ∈ Set.Ioo a b) (ha : a ∈ I) (hb : b ∈ J) :
    x ∈ (⟨I.lb, J.ub⟩ : Interval Dyadic) :=
  mem_bounds ha hx.1.le hx.2.le hb

end Inclusion
