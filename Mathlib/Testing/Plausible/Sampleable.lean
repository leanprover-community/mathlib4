/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Batteries.Data.Rat.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Monad
import Plausible.Sampleable

/-!
This module contains `Plausible.Shrinkable` and `Plausible.SampleableExt` instances for mathlib
types.
-/

namespace Plausible

open Random Gen

section Shrinkers

instance Rat.shrinkable : Shrinkable Rat where
  shrink r :=
    (Shrinkable.shrink r.num).bind fun d => Nat.shrink r.den |>.map fun n => Rat.divInt d n

end Shrinkers

section Samplers

open SampleableExt

instance Rat.sampleableExt : SampleableExt Rat :=
  mkSelfContained (do
    let d ← choose Int (-(← getSize)) (← getSize)
      (le_trans (Int.neg_nonpos_of_nonneg (Int.ofNat_zero_le _)) (Int.ofNat_zero_le _))
    let n ← choose Nat 0 (← getSize) (Nat.zero_le _)
    return Rat.divInt d n)

end Samplers

end Plausible
