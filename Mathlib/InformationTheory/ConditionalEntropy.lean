/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.InformationTheory.Entropy
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

open scoped Finset MeasureTheory NNReal ENNReal BigOperators
open InformationTheory

namespace InformationTheory

variable {α β : Type*}

/-- Conditional entropy `H(X | Y)` for a joint distribution on `α × β`. -/
noncomputable def condEntropy (p : PMF (α × β)) : ℝ :=
  entropy p - entropy (PMF.map Prod.snd p)

theorem cond_entropy_chain_rule {α β : Type*} (p : PMF (α × β)) :
    entropy p = entropy (PMF.map Prod.snd p) + condEntropy p := by
      simp only [condEntropy, add_sub_cancel]

end InformationTheory
