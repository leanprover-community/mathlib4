/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
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
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.T5

/-!
# Completion of a normed group

In this file we prove that the completion of a (semi)normed group is a normed group.

## Tags

normed group, completion
-/

@[expose] public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (E : Type*)

instance [UniformSpace E] [Norm E] : Norm (Completion E) where
  norm := Completion.extension Norm.norm

@[simp]
theorem norm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.extension_coe uniformContinuous_norm x

instance [SeminormedAddCommGroup E] : NormedAddCommGroup (Completion E) where
  dist_eq x y := by
    induction x, y using Completion.induction_on₂
    · refine isClosed_eq (Completion.uniformContinuous_extension₂ _).continuous ?_
      exact Continuous.comp Completion.continuous_extension (continuous_neg.fst.add continuous_snd)
    · rw [← Completion.coe_neg, ← Completion.coe_add, norm_coe, Completion.dist_eq,
        dist_eq_norm_neg_add]

@[simp]
theorem nnnorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖₊ = ‖x‖₊ := by
  simp [nnnorm]

@[simp]
lemma enorm_coe {E} [SeminormedAddCommGroup E] (x : E) : ‖(x : Completion E)‖ₑ = ‖x‖ₑ := by
  simp [enorm]

end Completion

end UniformSpace
