/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.LinearAlgebra.Matrix.Ideal
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

/-!
The matrix ring over a simple ring is simple
-/

@[expose] public section

namespace IsSimpleRing

variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]

instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
  simple := letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix |>.symm.isSimpleOrder

end IsSimpleRing
