/-
Copyright (c) 2024 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.KrullDimension

namespace Order

/-
These two lemmas could possibly be used to simplify the calculations in
the `Concrete calculations` section of `Mathlib/Order/KrullDimension.lean`, especially once
the `Set.encard` api is richer.
-/

proof_wanted height_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  height a = (Set.Iio a).encard

proof_wanted coheight_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  coheight a = (Set.Ioi a).encard

end Order
