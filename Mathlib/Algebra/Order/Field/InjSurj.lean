/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# Pulling back linearly ordered fields along injective maps
-/

open Function OrderDual

variable {α β : Type*}

namespace Function.Injective

@[deprecated (since := "2025-04-10")]
alias linearOrderedSemifield := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
alias linearOrderedField := Function.Injective.isStrictOrderedRing

end Function.Injective
