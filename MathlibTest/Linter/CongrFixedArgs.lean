import Mathlib.Tactic.Linter.CongrFixedArgs
import Mathlib.Init

set_option linter.congrFixedArgs true

def myMap (f : Nat → Nat) (l : List Nat) : List Nat := l.map f

/--
warning: The `@[congr]` theorem `myMap_congr` does not allow the following explicit arguments of `myMap` to change:
  `l : List Nat`
This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
@[congr]
theorem myMap_congr {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

-- Every explicit argument changes: no warning.
#guard_msgs in
@[congr]
theorem myMap_congr' {f g : Nat → Nat} {l l' : List Nat} (hl : l = l')
    (h : ∀ x ∈ l', f x = g x) : myMap f l = myMap g l' := by
  subst hl
  exact List.map_congr_left h

theorem myMap_congr'' {f g : Nat → Nat} {l : List Nat} (h : ∀ x ∈ l, f x = g x) :
    myMap f l = myMap g l :=
  List.map_congr_left h

/--
warning: The `@[congr]` theorem `myMap_congr''` does not allow the following explicit arguments of `myMap` to change:
  `l : List Nat`
This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
attribute [congr] myMap_congr''

def myZipWith (f : Nat → Nat → Nat) (l₁ l₂ : List Nat) : List Nat := List.zipWith f l₁ l₂

/--
warning: The `@[congr]` theorem `myZipWith_congr` does not allow the following explicit arguments of `myZipWith` to change:
  `l₁ : List Nat`
  `l₂ : List Nat`
This violates the recommendation in the documentation of `@[congr]`.

Note: This linter can be disabled with `set_option linter.congrFixedArgs false`
-/
#guard_msgs in
@[congr]
theorem myZipWith_congr {f g : Nat → Nat → Nat} {l₁ l₂ : List Nat} (h : ∀ a b, f a b = g a b) :
    myZipWith f l₁ l₂ = myZipWith g l₁ l₂ := by
  have : f = g := funext fun a ↦ funext (h a)
  rw [this]

def myGet (l : List Nat) (i : Nat) (_h : i < l.length) : Nat := l[i]

-- Proof arguments are ignored, even when they are the same on both sides.
#guard_msgs in
@[congr]
theorem myGet_congr {l l' : List Nat} {i i' : Nat} (hl : l = l') (hi : i = i')
    (h : i < l.length) : myGet l i h = myGet l' i' (hl ▸ hi ▸ h) := by
  subst hl hi
  rfl
