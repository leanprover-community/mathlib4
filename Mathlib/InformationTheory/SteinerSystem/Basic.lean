import Mathlib.Data.Finset.Card


structure Steiner (n1 n2 : ℕ) (C: Type*) : Type _ where
  carrier : Set (Finset C)
  blocks_have_size : ∀ b ∈ carrier, b.card = n2
  blocks_are_unique : ∀ s : Fin n1 ↪ C, ∃! b, b ∈ carrier ∧ Set.range s ⊆ b
