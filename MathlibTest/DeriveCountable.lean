import Mathlib.Tactic.DeriveCountable
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Tests of the `Countable` deriving handler
-/

namespace Test

/-!
Structure
-/
structure S (α β : Type*) where
  x : α
  y : List β
  deriving Countable

example : Countable (S Nat Bool) := inferInstance

/-!
Recursive inductive type, no indices
-/
inductive T (α : Type)
  | a (n : Option α)
  | b (n m : α) (t : T α)
  | c
  deriving Countable

example : Countable (T Nat) := inferInstance

/-!
Motivating example for writing the deriving handler
-/
inductive PreCantor' : Type
  | zero : PreCantor'
  | oadd : PreCantor' → ℕ+ → PreCantor' → PreCantor'
  deriving Countable

example : Countable PreCantor' := inferInstance

/-!
Sort
-/
inductive PList (α : Sort _) where
  | nil
  | cons (x : α) (xs : PList α)
  deriving Countable

example : Countable (PList (1 = 2)) := inferInstance

/-!
Recursive type with indices
-/

inductive I : Nat → Type
  | a (n : Nat) : I n
  | b (n : Nat) (x : Nat) (c : I x) : I (n + 1)
  deriving Countable

example : Countable (I 37) := inferInstance
example : Countable (Σ i, I i) := inferInstance

/-!
Mutually recursive types
-/
mutual
inductive T1 where
  | a
  | b (x : T1) (y : T2)
  deriving Countable
inductive T2 where
  | c (n : Nat)
  | d (x y : T1)
  deriving Countable
end

example : Countable T1 := inferInstance
example : Countable T2 := inferInstance


/-!
Not supported: nested inductive types
-/
/-- error: None of the deriving handlers for class `Countable` applied to `Nested` -/
#guard_msgs in
inductive Nested where
  | mk (xs : List Nested)
  deriving Countable

/-!
Not supported: reflexive inductive types
-/
/-- error: None of the deriving handlers for class `Countable` applied to `Reflex` -/
#guard_msgs in
inductive Reflex where
  | mk (f : Bool → Reflex)
  deriving Countable
