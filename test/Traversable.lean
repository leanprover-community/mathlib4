import Mathlib.Control.Traversable.Derive
import Mathlib.Control.Traversable.Instances

universe u

structure MyStruct (α : Type) where
  y : ℤ
  deriving Functor

inductive Either (α : Type u)
  | left : α → ℤ → Either α
  | right : α → Either α
  deriving Functor

structure MyStruct2 (α : Type u) : Type u where
  x : α
  y : ℤ
  η : List α
  k : List (List α)
  deriving Functor

inductive RecData (α : Type u) : Type u
  | nil : RecData α
  | cons : ℕ → α → RecData α → RecData α → RecData α
  deriving Functor
