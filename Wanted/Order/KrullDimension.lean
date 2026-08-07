module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.KrullDimension

namespace Order

/- These two lemmas could possibly be used to simplify the calculations in
`Mathlib/Order/KrullDimension.lean`, especially once the `Set.encard` api is richer. -/

proof_wanted height_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  height a = (Set.Iio a).encard

proof_wanted coheight_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  coheight a = (Set.Ioi a).encard

end Order
