/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# Finding the maximal rectangles in a list of points.
-/

/--
A rectangle `r` is a product of the left-closed, right-open intervals
`[r.left, r.right) × [r.bottom, r.top)`, whose corners are indexed by natural numbers.
-/
structure Rectangle where
  left : Nat
  right : Nat
  bottom : Nat
  top : Nat
deriving DecidableEq, Repr

namespace Rectangle

def width (r : Rectangle) : Nat := r.right - r.left
def height (r : Rectangle) : Nat := r.top - r.bottom

def toString (r : Rectangle) : String :=
  s!"[{r.left}, {r.right}) × [{r.bottom}, {r.top})"

instance : ToString Rectangle where
  toString := toString

instance instPointMembership : Membership (Nat × Nat) Rectangle where
  mem r x := r.left ≤ x.1 ∧ x.1 < r.right ∧ r.bottom ≤ x.2 ∧ x.2 < r.top

instance (x : Nat × Nat) (r : Rectangle) : Decidable (x ∈ r) := by
  dsimp [Membership.mem]
  infer_instance

/--
We say `r₁ ≤ r₂` if and only if every point in `r₁` is contained in `r₂`.
-/
instance instLE : LE Rectangle where
  le r₁ r₂ := r₁.width = 0 ∨ r₁.height = 0 ∨ ((r₁.left, r₁.bottom) ∈ r₂ ∧ (r₁.right - 1, r₁.top - 1) ∈ r₂)

instance : DecidableLE Rectangle := by
  dsimp [DecidableLE, LE.le, instLE]
  infer_instance

instance : Membership Rectangle (List (Nat × Nat)) where
  mem xs r := (List.range' r.left r.width).all fun x => (List.range' r.bottom r.height).all fun y => (x, y) ∈ xs

instance (r : Rectangle) (xs : List (Nat × Nat)) : Decidable (r ∈ xs) := by
  dsimp [Membership.mem]
  infer_instance

/--
Given a rectangle `r`, return the up to four four rectangles obtained from `r` by
- shifting the bottom left corner one coordinate to the left resp. bottom (if possible), or
- shifting the top right corner one coordinate to the right resp. top.
-/
def expansions (r : Rectangle) : List Rectangle :=
  (if r.left = 0 then [] else [{ r with left := r.left - 1 }]) ++
  (if r.bottom = 0 then [] else [{ r with bottom := r.bottom - 1 }]) ++
  [{ r with right := r.right + 1 }, { r with top := r.top + 1 }]

def area (r : Rectangle) : Nat := r.width * r.height

/--
The number of points in `r`, weighted by the function `w`.
-/
def weightedArea (r : Rectangle) (w : Nat × Nat → Nat) : Nat :=
  List.sum <|
    (List.range' r.left r.width).flatMap
      fun x => (List.range' r.bottom r.height).map fun y => w (x, y)

end Rectangle

/-- Find all (inclusion-)maximal rectangles contained within `xs`. -/
partial def maximalRectangles (xs : List (Nat × Nat)) : List Rectangle :=
  go [] (xs.map fun (x, y) => Rectangle.mk x (x+1) y (y+1))
where
  go (maximal : List Rectangle) (queue : List Rectangle) : List Rectangle :=
  match queue with
  | [] => maximal
  | r :: rs =>
    if maximal.any (r ≤ ·) then
      go maximal rs
    else
      match r.expansions.filter (· ∈ xs) with
      | [] => go (r :: maximal) rs
      | rs' => go maximal (rs' ++ rs)

/--
info: [{ left := 2, right := 3, bottom := 0, top := 3 },
 { left := 0, right := 1, bottom := 0, top := 3 },
 { left := 0, right := 3, bottom := 0, top := 2 }]
-/
#guard_msgs in
#eval maximalRectangles [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (2, 2)]
