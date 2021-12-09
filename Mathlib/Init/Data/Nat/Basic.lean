/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
import Mathlib.Init.Dvd

notation "ℕ" => Nat

namespace Nat

instance : Dvd ℕ where
  dvd a b := ∃ c, b = a * c

end Nat
