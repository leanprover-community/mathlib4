import Mathlib.Order.Interval.Finset.Basic

/-!
# Examples of finset builder notation
-/

open Finset

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-! ## `Data.Finset.Basic` -/

example (s : Finset α) : {x ∈ s | p x} = s.filter p := rfl

/-! ## `Data.Fintype.Basic` -/

section Fintype
variable [Fintype α]

example : ({x | p x} : Finset α) = univ.filter p := rfl
example : ({x : α | p x} : Finset α) = univ.filter p := rfl

-- If the type of `s` (or the entire expression) is `Finset ?α`, elaborate as `Finset`;
-- otherwise as `Set`
example (s : Finset α) : {x ∈ s | p x} = s.filter p := rfl
example (s : Finset α) : ({x ∈ s | p x} : Set α) = setOf fun x => x ∈ s ∧ p x := rfl
example (s : Finset α) : {x ∈ (s : Set α) | p x} = setOf fun x => x ∈ s ∧ p x := rfl

-- elaborate as `Set` if no expected type present
example : {x | p x} = setOf p := rfl
example : {x : α | p x} = setOf p := rfl

variable [DecidableEq α]

example (s : Finset α) : {x ∉ s | p x} = sᶜ.filter p := rfl
example (a : α) : ({x ≠ a | p x} : Finset α) = ({a}ᶜ : Finset α).filter p := rfl

-- elaborate as `Set` if the `s` or the expected type is not `Finset ?α`
example (s : Set α) : {x ∉ s | p x} = setOf fun x => x ∉ s ∧ p x := rfl
example (a : α) : {x ≠ a | p x} = setOf fun x => x ≠ a ∧ p x := rfl

end Fintype

/-! ## `Order.Interval.Finset.Basic` -/

section LocallyFiniteOrderBot
variable [Preorder α] [LocallyFiniteOrderBot α]

example (a : α) : ({x ≤ a | p x} : Finset α) = (Iic a).filter p := rfl
example (a : α) : ({x < a | p x} : Finset α) = (Iio a).filter p := rfl

-- elaborate as `Set` if the expected type is not `Finset ?α`
example (a : α) : {x ≤ a | p x} = setOf fun x => x ≤ a ∧ p x := rfl
example (a : α) : {x < a | p x} = setOf fun x => x < a ∧ p x := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [Preorder α] [LocallyFiniteOrderTop α]

example (a : α) : ({x ≥ a | p x} : Finset α) = (Ici a).filter p := rfl
example (a : α) : ({x > a | p x} : Finset α) = (Ioi a).filter p := rfl

-- elaborate as `Set` if the expected type is not `Finset ?α`
example (a : α) : {x ≥ a | p x} = setOf fun x => x ≥ a ∧ p x := rfl
example (a : α) : {x > a | p x} = setOf fun x => x > a ∧ p x := rfl

end LocallyFiniteOrderTop
