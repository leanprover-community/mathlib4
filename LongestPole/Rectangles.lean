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

instance instLE : LE Rectangle where
  le r₁ r₂ := r₁.width = 0 ∨ r₁.height = 0 ∨ ((r₁.left, r₁.bottom) ∈ r₂ ∧ (r₁.right - 1, r₁.top - 1) ∈ r₂)

instance : DecidableRel ((· : Rectangle) ≤ ·) := by
  dsimp [LE.le, instLE]
  infer_instance

instance : Membership Rectangle (List (Nat × Nat)) where
  mem xs r := (List.range' r.left r.width).all fun x => (List.range' r.bottom r.height).all fun y => (x, y) ∈ xs

instance (r : Rectangle) (xs : List (Nat × Nat)) : Decidable (r ∈ xs) := by
  dsimp [Membership.mem]
  infer_instance

def expansions (r : Rectangle) : List Rectangle :=
  (if r.left = 0 then [] else [{ r with left := r.left - 1 }]) ++
  (if r.bottom = 0 then [] else [{ r with bottom := r.bottom - 1 }]) ++
  [{ r with right := r.right + 1 }, { r with top := r.top + 1 }]

def area (r : Rectangle) : Nat := r.width * r.height

def weightedArea (r : Rectangle) (w : Nat × Nat → Nat) : Nat :=
  Nat.sum <|
    (List.range' r.left r.width).bind fun x => (List.range' r.bottom r.height).map fun y => w (x, y)

end Rectangle

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
      | [] => go (r::maximal) rs
      | rs' => go maximal (rs' ++ rs)

/--
info: [{ left := 2, right := 3, bottom := 0, top := 3 },
 { left := 0, right := 1, bottom := 0, top := 3 },
 { left := 0, right := 3, bottom := 0, top := 2 }]
-/
#guard_msgs in
#eval maximalRectangles [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (2, 2)]
