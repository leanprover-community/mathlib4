import Mathlib.Tactic.DeriveFintype

namespace tests

/-
Tests that the enumerable types succeed, even with universe levels.
-/

inductive A | x | y | z
  deriving Fintype

#check A.enumList

inductive A' : Type u | x | y | z
  deriving Fintype

#check A'.enumList

inductive A'' : Type 1 | x | y | z
  deriving Fintype

#check A''.enumList

/-
Now for general inductive types
-/

-- The empty type needs a little special handling due to needing `nomatch` syntactically
inductive B
  deriving Fintype

inductive C (α : Type _) | c (x : α)
  deriving Fintype

#synth Fintype (C Bool)

section
variable [Fintype α]
#synth Fintype (C α)
end

inductive D (p : Prop) | d (h : p)
  deriving Fintype

section
variable [Decidable q]
#synth Fintype (D q)
end

inductive baz | a : Bool → baz
  deriving Fintype

inductive bar (n : Nat) (α : Type)
  | a
  | b : Bool → bar n α
  | c (x : Fin n) : Fin x → bar n α
  | d : Bool → α → bar n α
  deriving Fintype

inductive Y : Nat → Type
  | x (n : Nat) : Y n
  deriving Fintype

structure S where
  (x y z : Bool)
  deriving Fintype

inductive MyOption (α : Type _)
  | none
  | some (x : α)
  deriving Fintype

-- Check implicits work
inductive I {α : Type _}
  | a | b {x : α}
  deriving Fintype

inductive I' {α : Type _}
  | a | b {x : α} : @I' α
  deriving Fintype

end tests
