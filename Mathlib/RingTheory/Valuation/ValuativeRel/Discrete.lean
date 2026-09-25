/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Normalized
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel

/-! # Discrete `ValuativeRel`s.

# Main results

* `ValuativeRel.valuation_isRankOneDiscrete_iff` : a `ValuativeRel` `wr` is discrete, nontrivial
  and has rank less than or equal to one if and only if `wr.valuation` is rank one discrete.

## Tags

valuation, discrete, normalized

-/

@[expose] public section

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

namespace ValuativeRel

open Valuation

variable {F Γ : Type*} [CommRing F] [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)

instance instIsRankOneDiscrete [hw : w.IsRankOneDiscrete] :
    (ofValuation w).valuation.IsRankOneDiscrete :=
  isRankOneDiscrete_of_isEquiv (isEquiv_ofValuation w)

instance instIsRankLeOneOfIsRankOneDiscrete [hw : w.IsRankOneDiscrete] :
    (ofValuation w).IsRankLeOne F := by
  let := ofValuation w
  exact isRankLeOne_of_rankOne (h := (instIsRankOneDiscrete w).rankOne _ one_lt_two)

instance instIsDiscreteOfIsRankOneDiscrete [w.IsRankOneDiscrete] :
    (ofValuation w).IsDiscrete F := by
  let wr := ofValuation w
  let hw : wr.valuation.normalized.IsEquiv wr.valuation := (Valuation.normalized_isEquiv _).symm
  rw [← compatible_iff_isEquiv] at hw
  exact IsDiscrete.of_compatible_withZeroMulInt wr.valuation.normalized

instance (Fq : Type*) [Field Fq] [Algebra Fq F] [IsTrivialOn Fq w] :
    IsTrivialOn Fq (ofValuation w).valuation :=
  (isEquiv_ofValuation w).isTrivialOn inferInstance

open WithZero MonoidWithZeroHom ValueGroup₀

instance valuation_isRankOneDiscrete (wr : ValuativeRel F) [hd : wr.IsDiscrete]
    [ht : wr.IsNontrivial] [hr : wr.IsRankLeOne] :
    IsRankOneDiscrete wr.valuation := by
  rw [← nonempty_valueGroup₀_orderMonoidIso_withZeroMulInt_iff]
  have : Nonempty (ValueGroupWithZero F ≃*o WithZero (Multiplicative ℤ)) := by
    rw [ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff]
    exact ⟨hd, ht, inferInstance⟩
  exact ⟨(ValueGroupWithZero.orderMonoidIso (valuation F)).symm.trans this.some⟩

lemma valuation_isRankOneDiscrete_iff (wr : ValuativeRel F) :
    wr.IsDiscrete ∧ wr.IsNontrivial ∧ wr.IsRankLeOne ↔ IsRankOneDiscrete wr.valuation := by
  refine ⟨fun ⟨hd, ht, hr⟩ ↦ valuation_isRankOneDiscrete wr, fun h ↦ ⟨?_,
    (isNontrivial_iff_isNontrivial wr.valuation).mpr (IsRankOneDiscrete.instIsNontrivial _),
    isRankLeOne_of_rankOne (h := h.rankOne _ one_lt_two)⟩⟩
  let hw : wr.valuation.normalized.IsEquiv wr.valuation := (Valuation.normalized_isEquiv _).symm
  rw [← compatible_iff_isEquiv] at hw
  exact IsDiscrete.of_compatible_withZeroMulInt wr.valuation.normalized

end ValuativeRel
