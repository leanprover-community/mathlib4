import Mathlib.Tactic.Linter.CongrFixedArgs
import Mathlib.Init

set_option linter.congrFixedArgs true

def myMap (f : Nat → Nat) (l : List Nat) : List Nat := l.map f

-- `l` is the same on both sides.
/--
warning: The `@[congr]` theorem `myMap_congr` does not allow the following explicit arguments of `myMap` to change: `l` (argument #2). This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
@[congr]
theorem myMap_congr {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

-- Every explicit argument may change: no warning.
#guard_msgs in
@[congr]
theorem myMap_congr' {f g : Nat → Nat} {l l' : List Nat} (hl : l = l')
    (h : ∀ x ∈ l', f x = g x) : myMap f l = myMap g l' := by
  subst hl
  exact List.map_congr_left h

theorem myMap_congr'' {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

-- The attribute can also be added with the `attribute` command.
/--
warning: The `@[congr]` theorem `myMap_congr''` does not allow the following explicit arguments of `myMap` to change: `l` (argument #2). This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
attribute [congr] myMap_congr''

def myGet (l : List Nat) (i : Nat) (_h : i < l.length) : Nat := l[i]

-- Proof arguments are ignored, even when they are the same on both sides.
#guard_msgs in
@[congr]
theorem myGet_congr {l l' : List Nat} {i i' : Nat} (hl : l = l') (hi : i = i')
    (h : i < l.length) : myGet l i h = myGet l' i' (hl ▸ hi ▸ h) := by
  subst hl hi
  rfl
