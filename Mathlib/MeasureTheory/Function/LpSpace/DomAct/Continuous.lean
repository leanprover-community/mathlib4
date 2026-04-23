/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.Topology.Algebra.Constructions.DomMulAct
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Continuity of the action of `Mᵈᵐᵃ` on `MeasureSpace.Lp E p μ`

In this file we prove that under certain conditions,
the action of `Mᵈᵐᵃ` on `MeasureTheory.Lp E p μ` is continuous in both variables.

Recall that `Mᵈᵐᵃ` acts on `MeasureTheory.Lp E p μ`
by `mk c • f = MeasureTheory.Lp.compMeasurePreserving (c • ·) _ f`.
This action is defined, if `M` acts on `X` by measure-preserving maps.

If `M` acts on `X` by continuous maps
preserving a locally finite measure
which is inner regular for finite measure sets with respect to compact sets,
then the action of `Mᵈᵐᵃ` on `Lp E p μ` described above, `1 ≤ p < ∞`,
is continuous in both arguments.

In particular, it applies to the case when `X = M` is a locally compact topological group,
and `μ` is the Haar measure.

## Tags

measure theory, group action, domain action, continuous action, Lp space
-/

@[expose] public section

open scoped ENNReal
open DomMulAct

namespace MeasureTheory

variable {X M E : Type*}
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [Monoid M] [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [SMul M X] [ContinuousSMul M X]
  [NormedAddCommGroup E]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [SMulInvariantMeasure M X μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [hp : Fact (p ≠ ∞)]

@[to_additive]
instance Lp.instContinuousSMulDomMulAct : ContinuousSMul Mᵈᵐᵃ (Lp E p μ) where
  continuous_smul :=
    let g : C(Mᵈᵐᵃ × Lp E p μ, C(X, X)) :=
      (ContinuousMap.mk (fun a : M × X ↦ a.1 • a.2) continuous_smul).curry.comp <|
        .comp (.mk DomMulAct.mk.symm) ContinuousMap.fst
    continuous_snd.compMeasurePreservingLp g.continuous _ Fact.out

end MeasureTheory
