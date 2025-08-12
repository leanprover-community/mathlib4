/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.RankOne

/-!
# p-adic numbers with a valuative relation

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

variable {p : ℕ} [hp : Fact p.Prime] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation ℚ_[p] Γ₀)

open ValuativeRel WithZero

namespace Padic

-- TODO: should this be automatic from a nonarchimedean nontrivially normed field?
instance : ValuativeRel ℚ_[p] := .ofValuation mulValuation

instance : Valuation.Compatible (mulValuation (p := p)) := .ofValuation _

variable [v.Compatible]

lemma valuation_p_ne_zero : v p ≠ 0 := by
  simp [(isEquiv v (Padic.mulValuation)).ne_zero, hp.out.ne_zero]

@[simp]
lemma valuation_p_lt_one : v p < 1 := by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, ← lt_log_iff_exp_lt]

instance : IsNontrivial ℚ_[p] where
  condition := ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

instance : IsRankLeOne ℚ_[p] := .of_compatible_mulArchimedean mulValuation

end Padic
