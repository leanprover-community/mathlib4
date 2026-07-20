/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.StageZeroInternalOrder
public import Mathlib.SetTheory.ZFC.Constructible.RudimentarySuccessorInternalOrder

/-!
# Internally represented well-orders of finite constructible stages

The zero-stage graph and the successor construction give the result for every
finite ordinal without any limit-stage coding assumption.
-/

@[expose] public section

universe u

namespace Constructible.Model

/-- Every finite constructible stage has a well-order graph belonging to `L`. -/
theorem finiteStageInternallyWellOrdered (n : Nat) :
    StageInternallyWellOrdered (n : Ordinal.{u}) := by
  induction n with
  | zero =>
      exact stageZeroInternallyWellOrdered
  | succ n ih =>
      rw [Nat.cast_add_one, ← Order.succ_eq_add_one]
      exact stageSuccInternallyWellOrdered (n : Ordinal.{u}) ih

end Constructible.Model
