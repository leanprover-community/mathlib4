/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/

/-- `Const κ α = κ`. The constant functor with value `κ`. -/
def Const (κ : Type u) (_α : Type v) : Type u := κ

namespace Const

instance : Functor (Const κ) where
  map _ k := k

/-!
# Using const as a writer.

If we think of `κ` as a monoid then there is a nice applicative structure that
we can add to it. You can interpret the applicative structure as returning the
product of all of the `κ`s.

As with `WriterT`, `∅, ++` is preferred to `1, *` as the monoid.
-/

instance [EmptyCollection κ] : Pure (Const κ) where
  pure _ := (∅ : κ)

instance [EmptyCollection κ] [Append κ] : Applicative (Const κ) where
  seq (f : κ) (x : Unit → κ) := f ++ x ()

end Const

/-- AKA `Copure`. -/
class Extract (F : Type u → Type v) where
  extract {α} : F α → α

export Extract (extract)

/-- AKA `Cobind`. -/
class Extend (F : Type u → Type v) where
  extend {α β} : (F α → β) → F α → F β

class Comonad (F : Type u → Type v) extends Extract F, Extend F
