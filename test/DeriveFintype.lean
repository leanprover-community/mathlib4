import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

set_option autoImplicit true
namespace tests

/-
Tests that the enumerable types succeed, even with universe levels.
-/

inductive A | x | y | z
  deriving Fintype

/--
info: tests.A.enumList : List A
-/
#guard_msgs in
#check A.enumList

inductive A' : Type u | x | y | z
  deriving Fintype

/--
info: tests.A'.enumList.{u} : List A'
-/
#guard_msgs in
#check A'.enumList

inductive A'' : Type 1 | x | y | z
  deriving Fintype

/--
info: tests.A''.enumList : List A''
-/
#guard_msgs in
#check A''.enumList

/-
Now for general inductive types
-/

-- The empty type needs a little special handling due to needing `nomatch` syntactically
inductive B
  deriving Fintype

example : (Finset.univ : Finset B) = ∅ := rfl

inductive C (α : Type _) | c (x : α)
  deriving Fintype, DecidableEq

/--
info: instFintypeC
-/
#guard_msgs in
#synth Fintype (C Bool)

example : (Finset.univ : Finset (C Bool)) = Finset.univ.image .c := rfl

inductive C' (P : Prop) | c (h : P)
  deriving Fintype

/-- info: instFintypeC'OfDecidable -/
#guard_msgs in
#synth Fintype (C' (1 = 2))

example : Fintype.card (C' (1 = 2)) = 0 := rfl

inductive C'' (P : Prop) | c (h : P) (b : Bool)
  deriving Fintype

example : Fintype.card (C'' (1 = 2)) = 0 := rfl

section
variable [Fintype α]

/--
info: instFintypeC
-/
#guard_msgs in
#synth Fintype (C α)
end

inductive D (p : Prop) | d (h : p)
  deriving Fintype

section
variable [Decidable q]

/-- info: instFintypeDOfDecidable -/
#guard_msgs in
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

example : Fintype.card S = 8 := rfl

inductive MyOption (α : Type _)
  | none
  | some (x : α)
  deriving Fintype

example : Fintype.card (MyOption Bool) = 3 := rfl

-- Check implicits work
inductive I {α : Type _}
  | a | b {x : α}
  deriving Fintype

inductive I' {α : Type _}
  | a | b {x : α} : @I' α
  deriving Fintype

/-
`derive_fintype%`
-/

def myBoolInst := derive_fintype% Bool

example : Fintype Bool := myBoolInst

def myBoolInst' : Fintype Bool := derive_fintype% _

example : Fintype Bool := myBoolInst'

def myProdInst [Fintype α] [Fintype β] : Fintype (α × β) := derive_fintype% _

structure MySubtype (s : Set α) where
  val : α
  mem : val ∈ s
  --deriving Fintype -- fails

instance (s : Set α) [Fintype α] [DecidablePred (· ∈ s)] : Fintype (MySubtype s) :=
  derive_fintype% _

/-
Tests from mathlib 3
-/

inductive Alphabet
  | a | b | c | d | e | f | g | h | i | j | k | l | m
  | n | o | p | q | r | s | t | u | v | w | x | y | z
  | A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  deriving Fintype

example : Fintype.card Alphabet = 52 := rfl

inductive foo
  | A (x : Bool)
  | B (y : Unit)
  | C (z : Fin 37)
  deriving Fintype

example : Fintype.card foo = 2 + 1 + 37 := rfl

inductive foo2 (α : Type)
  | A : α → foo2 α
  | B : α → α → foo2 α
  | C : α × α → foo2 α
  | D : foo2 α
  deriving Fintype

inductive foo3 (α β : Type) (n : ℕ)
  | A : (α → β) → foo3 α β n
  | B : Fin n → foo3 α β n
  --deriving Fintype -- won't work because missing decidable instance

instance (α β : Type) [DecidableEq α] [Fintype α] [Fintype β] (n : ℕ) : Fintype (foo3 α β n) :=
  derive_fintype% _

structure foo4 {m n : Type} (b : m → ℕ) where
  (x : m × n)
  (y : m × n)
  (h : b x.1 = b y.1)
  deriving Fintype

class MyClass (M : Type _) where
  (one : M)
  (eq_one : ∀ x : M, x = one)

instance {M : Type _} [Fintype M] [DecidableEq M] : Fintype (MyClass M) :=
  derive_fintype% _

end tests
