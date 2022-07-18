import Mathlib.Tactic.TypeCheck

example : True := by {
  type_check Nat; -- Type
  type_check Bool.true; -- Bool
  type_check nat_lit 1; -- Nat
  type_check (1 : Nat); -- Nat
  type_check (True : _); -- Prop
  type_check ∀ x y : Nat, x = y; -- Prop
  type_check fun x : Nat => 2 * x + 1; -- Nat -> Nat
  exact True.intro }
