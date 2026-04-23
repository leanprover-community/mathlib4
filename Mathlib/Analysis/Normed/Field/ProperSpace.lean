/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Proper nontrivially normed fields

Nontrivially normed fields are `ProperSpaces` when they are `WeaklyLocallyCompact`.

## Main results

* `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`

## Implementation details

This is a special case of `ProperSpace.of_locallyCompactSpace` from
`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`, specialized to be on the field itself
with a proof that requires fewer imports.
-/

public section

assert_not_exists FiniteDimensional

open Metric Filter

/-- A weakly locally compact normed field is proper.
This is a specialization of `ProperSpace.of_locallyCompactSpace`
which holds for `NormedSpace`s but requires more imports. -/
lemma ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [WeaklyLocallyCompactSpace 𝕜] :
    ProperSpace 𝕜 := by
  rcases exists_isCompact_closedBall (0 : 𝕜) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC n : IsCompact (closedBall (0 : 𝕜) (‖c‖ ^ n * r)) := by
    have : c ^ n ≠ 0 := pow_ne_zero _ <| fun h ↦ by simp [h, zero_le_one.not_gt] at hc
    convert hr.smul (c ^ n)
    ext
    simp only [mem_closedBall, dist_zero_right, Set.mem_smul_set_iff_inv_smul_mem₀ this,
      smul_eq_mul, norm_mul, norm_inv, norm_pow,
      inv_mul_le_iff₀ (by simpa only [norm_pow] using norm_pos_iff.mpr this)]
  have hTop : Tendsto (fun n ↦ ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)
