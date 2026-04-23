/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Convergence of `p`-series (complex case)

Here we show convergence of `∑ n : ℕ, 1 / n ^ p` for complex `p`. This is done in a separate file
rather than in `Analysis.PSeries` in order to keep the prerequisites of the former relatively light.

## Tags

p-series, Cauchy condensation test
-/

public section

lemma Complex.summable_one_div_nat_cpow {p : ℂ} :
    Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ p) ↔ 1 < re p := by
  rw [← Real.summable_one_div_nat_rpow, ← summable_nat_add_iff 1 (G := ℝ),
    ← summable_nat_add_iff 1 (G := ℂ), ← summable_norm_iff]
  simp only [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr <| Nat.succ_pos _)]
