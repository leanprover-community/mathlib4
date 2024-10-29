/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.Vector

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

instance : DecidableRel ((· : Rectangle) ≤ ·) := by
  dsimp [LE.le, instLE]
  infer_instance

def subset (r : Rectangle) (xs : List (Nat × Nat)) :=
  (List.range' r.left r.width).all fun x => (List.range' r.bottom r.height).all fun y => (x, y) ∈ xs

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
  Nat.sum <|
    (List.range' r.left r.width).bind fun x => (List.range' r.bottom r.height).map fun y => w (x, y)

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
      match r.expansions.filter (·.subset xs) with
      | [] => go (r :: maximal) rs
      | rs' => go maximal (rs' ++ rs)

/--
info: [{ left := 2, right := 3, bottom := 0, top := 3 },
 { left := 0, right := 1, bottom := 0, top := 3 },
 { left := 0, right := 3, bottom := 0, top := 2 }]
-/
#guard_msgs in
#eval maximalRectangles [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (2, 2)]

namespace Fin

/-- Check that `f i` is true for all `i : Fin n`, short-circuiting on `false`. -/
def all : ∀ {n} (_ : Fin n → Bool), Bool
  | 0, _ => true
  | (n + 1), f => f ⟨0, by omega⟩ && all (f ∘ Fin.succ)

-- make tail-recursive
def find? : ∀ {n} (_ : Fin n → Bool), Option (Fin n)
  | 0, _ => none
  | (n + 1), f => if f ⟨0, by omega⟩ then some ⟨0, by omega⟩ else (find? (f ∘ Fin.succ)).map Fin.succ

end Fin

namespace BitVec

/-- Check if `f i` is true for all `i` such that `xs[i]` is true.-/
def all {w} (xs : BitVec w) (f : Fin w → Bool) : Bool :=
  Fin.all fun i => !xs[i] || f i

def map {w} (xs : BitVec w) {α} (f : Fin w → α) : List α :=
  Fin.foldr w (init := []) fun i acc => if xs[i] then f i :: acc else acc

def filterMap {w} (xs : BitVec w) {α} (f : Fin w → Option α) : List α :=
  Fin.foldr w (init := []) fun i acc => if xs[i] then match f i with
    | some a => a :: acc
    | none => acc
    else acc

def find? {w} (xs : BitVec w) (p : Fin w → Bool) : Option (Fin w) :=
  Fin.find? fun i => xs[i] && p i

def foldr {w} {α} (xs : BitVec w) (f : Fin w → α → α) (init : α) : α :=
  Fin.foldr w (init := init) fun i acc => if xs[i] then f i acc else acc

def popCount {n} (xs : BitVec n) : Nat :=
  xs.foldr (init := 0) fun _ acc => acc + 1

end BitVec

open Batteries (Vector)

structure NatNatSet (n : Nat) where
  points : Vector (BitVec n) n

namespace NatNatSet

instance (n) : EmptyCollection (NatNatSet n) where
  emptyCollection := ⟨.mkVector n 0⟩

def map {n} {α} (f : Fin n → Fin n → α) (s : NatNatSet n) : List α :=
  Fin.foldr n (init := []) fun x acc => s.points[x].foldr (init := acc) fun y acc => f x y :: acc

def ofList (n : Nat) (pts : List (Nat × Nat)) : NatNatSet n :=
  pts.foldl (init := ∅) fun s ⟨x, y⟩ =>
    if hx : x < n then
      ⟨s.points.set ⟨x, hx⟩ (s.points[x] ||| BitVec.twoPow n y)⟩
    else
      s

end NatNatSet

/--
A generalized rectangle `r` is a product of two sets of natural numbers.
-/
structure GeneralizedRectangle (n : Nat) where
  xs : BitVec n
  ys : BitVec n
deriving DecidableEq, Repr

namespace GeneralizedRectangle

variable {n : Nat}

def singleton {n} (x y : Fin n) : GeneralizedRectangle n :=
  { xs := BitVec.twoPow n x, ys := BitVec.twoPow n y }

def toString (r : GeneralizedRectangle n) : String :=
  s!"{r.xs} × {r.ys}"

instance : ToString (GeneralizedRectangle n) where
  toString := toString

instance instPointMembership : Membership (Nat × Nat) (GeneralizedRectangle n) where
  mem r x := r.xs.getLsbD x.1 && r.ys.getLsbD x.2

instance (x : Nat × Nat) (r : GeneralizedRectangle n) : Decidable (x ∈ r) := by
  dsimp [Membership.mem]
  infer_instance

/--
We say `r₁ ≤ r₂` if and only if every point in `r₁` is contained in `r₂`.
-/
instance instLE : LE (GeneralizedRectangle n) where
  le r₁ r₂ := (r₁.xs ||| r₂.xs = r₂.xs) && (r₁.ys ||| r₂.ys = r₂.ys)

instance : DecidableRel ((· : GeneralizedRectangle n) ≤ ·) := by
  dsimp [LE.le, instLE]
  infer_instance

def subset (r : GeneralizedRectangle n) (s : NatNatSet n) :=
  r.xs.all fun x => (s.points[x] ||| r.ys) = s.points[x]

/--
Given a rectangle `r`, return the up to four four rectangles obtained from `r` by
- shifting the bottom left corner one coordinate to the left resp. bottom (if possible), or
- shifting the top right corner one coordinate to the right resp. top.
-/
def expansionsWithin (r : GeneralizedRectangle n) (s : NatNatSet n) : List (GeneralizedRectangle n) :=
  ((~~~r.xs).filterMap fun x => if (s.points[x] ||| r.ys) = s.points[x] then some { r with xs := r.xs ||| BitVec.twoPow n x } else none) ++
  ((~~~r.ys).filterMap fun y => if (r.xs.all fun x => s.points[x][y]) then some { r with ys := r.ys ||| BitVec.twoPow n y } else none)

def area (r : GeneralizedRectangle n) : Nat := r.xs.popCount * r.ys.popCount

end GeneralizedRectangle

variable {n : Nat}

/-- Find all (inclusion-)maximal generalized rectangles contained within `xs`. -/
partial def maximalGeneralizedRectangles (pts : NatNatSet n) : List (GeneralizedRectangle n) :=
  go [] [(n, GeneralizedRectangle.mk 0 (.allOnes _))]
where
  go (maximal : List (GeneralizedRectangle n)) (queue : List (Nat × GeneralizedRectangle n)) :
    List (GeneralizedRectangle n) :=
  match queue with
  | [] => maximal.pwFilter (fun r₁ r₂ => (! r₁ ≤ r₂) && (! r₂ ≤ r₁))
  | (k, r) :: rs =>
    let next := (List.range k).filterMap fun i =>
      let ys := r.ys &&& pts.points[i]!
      if ys = 0 then none else some (i, { xs := r.xs ||| BitVec.twoPow n i, ys := ys })
    if next.isEmpty then
      if maximal.any (r ≤ ·) then
        go maximal rs
      else
        go (r :: maximal.filter (! · ≤ r)) rs
    else
      go maximal (next ++ rs)

def board := NatNatSet.ofList 3 [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (2, 2)]

/-- info: [{ xs := 0x7#3, ys := 0x3#3 }, { xs := 0x5#3, ys := 0x7#3 }] -/
#guard_msgs in
#eval maximalGeneralizedRectangles board
