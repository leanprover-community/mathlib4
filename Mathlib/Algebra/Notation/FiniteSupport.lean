import Mathlib.Data.Finite.Defs

/-!
# Finiteness of support
-/

public section

assert_not_exists Monoid

namespace Function
variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : (mulSupport f).Finite) :
    (mulSupport fun b ↦ f (a, b)).Finite :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function
