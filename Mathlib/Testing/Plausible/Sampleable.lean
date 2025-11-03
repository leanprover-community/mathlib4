/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.Monad
import Mathlib.Data.PNat.Defs
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
    (Shrinkable.shrink r.num).flatMap fun d => Nat.shrink r.den |>.map fun n => Rat.divInt d n

instance PNat.shrinkable : Shrinkable PNat where
  shrink m := Nat.shrink m.natPred |>.map Nat.succPNat

end Shrinkers

section Samplers

open SampleableExt

instance Rat.sampleableExt : SampleableExt Rat :=
  mkSelfContained (do
    let d ← choose Int (-(← getSize)) (← getSize)
      (le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
    let n ← choose Nat 0 (← getSize) (Nat.zero_le _)
    return Rat.divInt d n)


instance PNat.sampleableExt : SampleableExt PNat :=
  mkSelfContained (do
    let n ← chooseNat
    return Nat.succPNat n)

end Samplers

end Plausible
