/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.Valuation.RankOne
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
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# p-adic numbers with a valuative relation

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

@[expose] public section

variable {p : ℕ} [hp : Fact p.Prime] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation ℚ_[p] Γ₀)

open ValuativeRel WithZero

namespace Padic

-- TODO: should this be automatic from a nonarchimedean nontrivially normed field?
noncomputable instance : ValuativeRel ℚ_[p] := .ofValuation mulValuation

instance : Valuation.Compatible (mulValuation (p := p)) := .ofValuation _

variable [v.Compatible]

lemma valuation_p_ne_zero : v p ≠ 0 := by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]
lemma valuation_p_lt_one : v p < 1 := by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, inv_lt_one₀,
    ← log_lt_iff_lt_exp]

instance : IsNontrivial ℚ_[p] where
  condition := ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

instance : IsRankLeOne ℚ_[p] := .of_compatible_mulArchimedean mulValuation

end Padic
