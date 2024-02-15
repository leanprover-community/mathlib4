/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Function.Support
import Mathlib.Data.Set.Finite

/-!
# Finiteness of support
-/

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : (mulSupport f).Finite) :
    (mulSupport fun b ↦ f (a, b)).Finite :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)
#align function.mul_support_along_fiber_finite_of_finite Function.mulSupport_along_fiber_finite_of_finite
#align function.support_along_fiber_finite_of_finite Function.support_along_fiber_finite_of_finite

end Function
