import Mathlib.Mathport.Notation
import Mathlib.Init.Data.Nat.Lemmas

namespace Test

-- set_option trace.notation3 true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

#check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
#check ∀ᶠ x in Filter.atTop, x < 3


notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
#check ∃' x < 3, x < 3

def func (x : α) : α := x
notation3 "func! " (...) ", " r:(scoped p => func p) => r
-- Make sure it handles additional arguments. Should not consume `(· * 2)`.
-- Note: right now this causes the notation to not pretty print at all.
#check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit
notation3 "~{" (x"; "* => foldl (a b => Prod.mk a b) MyUnit) "}~" => x
#check ~{1; true; ~{2}~}~
#check ~{}~

notation3 "%[" (x", "* => foldr (a b => List.cons a b) List.nil) "]" => x
#check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation3 "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
#check *[1] (x) (y), x + y
#check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation3 "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
#check *'[1] (x) (y), x + y
#check bar' 1

-- Currently does not pretty print due to pi type
notation3 (prettyPrint := false) "MyPi " (...) ", " r:(scoped p => (x : _) → p x) => r
#check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation3 "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
#check BAD 1; 2, 3 DAB
