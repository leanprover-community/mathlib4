import Mathlib

namespace Tuple
variable {n}
variable {α : (i : Fin n) → Type*}
variable [Monoid ((i : Fin n) → α i)]
variable [∀ i, Monoid (α i)]

#check Prod.orderOf_mk

@[to_additive]
lemma orderOf_eq (a : (i : Fin n) → α i)  : orderOf a = Finset.univ.lcm (fun i => orderOf (a i)) :=
  sorry
end Tuple
