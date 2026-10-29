import Mathlib.Tactic.DeriveEncodable

/-!
# Tests for the `Encodable` deriving handler
-/

/-!
Structures
-/
structure Struct where
  x : Nat
  y : Bool
  deriving Encodable

example : Encodable Struct := inferInstance


/-!
Inductive types with parameters
-/

inductive T (α : Type) where
  | a (x : α) (y : Bool) (z : T α)
  | b
  deriving Encodable, Repr

example : Encodable (T Nat) := inferInstance
/--
error: failed to synthesize instance of type class
  Encodable (ℕ → Bool)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in example : Encodable (Nat → Bool) := inferInstance

/-- info: 96964472478917 -/
#guard_msgs in
#eval Encodable.encode <| T.a 3 true T.b

/-- info: some (T.a 3 true (T.b)) -/
#guard_msgs in
#eval (Encodable.decode 96964472478917 : Option <| T Nat)


/-!
Mutually recursive types
-/
mutual
inductive T1 where
  | a
  | b (x : T1) (y : T2)
  deriving Encodable
inductive T2 where
  | c (n : Nat)
  | d (x y : T1)
  deriving Encodable
end

example : Encodable T1 := inferInstance
example : Encodable T2 := inferInstance


/-!
Not supported: indexed types
-/
/-- error: None of the deriving handlers for class `Encodable` applied to `Idx` -/
#guard_msgs in
inductive Idx : Nat → Type where
  | a (i : Nat) (j : Nat) : Idx (i + j)
  deriving Encodable

/-!
Not supported: nested inductive types
-/
/-- error: None of the deriving handlers for class `Encodable` applied to `Nested` -/
#guard_msgs in
inductive Nested where
  | mk (xs : List Nested)
  deriving Encodable

/-!
Not supported: reflexive inductive types
-/
/-- error: None of the deriving handlers for class `Encodable` applied to `Reflex` -/
#guard_msgs in
inductive Reflex where
  | mk (f : Bool → Reflex)
  deriving Encodable
