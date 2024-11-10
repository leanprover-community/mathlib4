/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.Vector
import Mathlib.Data.List.GroupBy

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
  le r₁ r₂ := r₁.width = 0 ∨ r₁.height = 0 ∨
    ((r₁.left, r₁.bottom) ∈ r₂ ∧ (r₁.right - 1, r₁.top - 1) ∈ r₂)
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

namespace List

def finEnum {α} (xs : List α) : List (Fin xs.length × α) :=
  .ofFn fun i => ⟨i, xs[i]⟩

@[simp] theorem length_finEnum {α} {xs : List α} : xs.finEnum.length = xs.length := by
  simp [finEnum]

@[simp] theorem getElem_finEnum {α} {xs : List α} {i : Nat} (h : i < xs.finEnum.length) :
    xs.finEnum[i] = ⟨⟨i, by simpa using h⟩, xs[i]'(by simpa using h)⟩ := by
  simp [finEnum]

@[simp] theorem getElem?_finEnum {α} {xs : List α} {i : Nat} :
    xs.finEnum[i]? =
      xs[i]?.attach.map fun ⟨x, m⟩ => ⟨⟨i, by simp [getElem?_eq_some] at m; exact m.1⟩, x⟩ := by
  symm
  by_cases h' : i < xs.finEnum.length
  · simp [getElem?_eq_getElem h']
  · rw [getElem?_eq_none (l := xs.finEnum)]
    <;> simp_all

end List

open Batteries (Vector)

namespace Batteries.Vector

attribute [simp] Vector.size_eq

@[simp] theorem length_toList {α n} (xs : Vector α n) : xs.toList.length = n :=
  xs.size_eq

@[simp] theorem getElem_toArray {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := by
  cases xs
  simp

@[simp] theorem getElem_toList {α n} (xs : Vector α n) (i : Nat) (h : i < xs.toList.length) :
    xs.toList[i] = xs[i]'(by simpa using h) := by
  simp [toList]

@[simp] theorem getElem_ofFn {α n} (f : Fin n → α) (i : Nat) (h : i < n) :
    (Vector.ofFn f)[i] = f ⟨i, by simpa using h⟩ := by
  simp [ofFn]

def finEnum {α n} (xs : Vector α n) : Vector (Fin n × α) n :=
  .ofFn fun i => ⟨i, xs[i]⟩

@[simp] theorem toList_finEnum {α n} (xs : Vector α n) :
    xs.finEnum.toList = xs.toList.finEnum.map fun ⟨i, x⟩ => ⟨Fin.cast (by simp) i, x⟩ := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp [finEnum]

end Batteries.Vector

namespace Fin

/-- Check that `f i` is true for all `i : Fin n`, short-circuiting on `false`. -/
def all : ∀ {n} (_ : Fin n → Bool), Bool
  | 0, _ => true
  | (n + 1), f => f ⟨0, by omega⟩ && all (f ∘ Fin.succ)

@[simp] theorem all_eq {n} (f : Fin n → Bool) :
    Fin.all f = decide (∀ i, f i) := by
  induction n with
  | zero =>
    simp only [all, true_eq_decide_iff]
    rintro ⟨-, ⟨⟩⟩
  | succ n ih =>
    simp [all, ih, Fin.forall_fin_succ]

-- make tail-recursive
def find? : ∀ {n} (_ : Fin n → Bool), Option (Fin n)
  | 0, _ => none
  | (n + 1), f =>
    if f ⟨0, by omega⟩ then
      some ⟨0, by omega⟩
    else
      (find? (f ∘ Fin.succ)).map Fin.succ

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

def ofListNat (n : Nat) (xs : List Nat) : BitVec n :=
  xs.foldl (init := 0) fun acc x => if x < n then acc ||| BitVec.twoPow n x else acc

instance {n} : HasSubset (BitVec n) where
  Subset xs ys := xs &&& ys = xs

instance {n} : DecidableRel ((· : BitVec n) ⊆ ·) := by
  dsimp [Subset, instLE]
  infer_instance

def ofFnLE {n} (f : Fin n → Bool) : BitVec n :=
  BitVec.cast (by simp) (BitVec.ofBoolListLE <| List.ofFn f)

instance {n} : Hashable (BitVec n) where
  hash v := hash v.toNat

end BitVec

open Batteries (Vector)

variable {n m : Nat}

structure BipartiteGraph (n m : Nat) where
  edges : Vector (BitVec m) n

namespace BipartiteGraph

instance : EmptyCollection (BipartiteGraph n m) where
  emptyCollection := ⟨.mkVector n 0⟩

def map {α} (f : Fin n → Fin m → α) (s : BipartiteGraph n m) : List α :=
  Fin.foldr n (init := []) fun x acc => s.edges[x].foldr (init := acc) fun y acc => f x y :: acc

def ofList (n m : Nat) (pts : List (Nat × Nat)) : BipartiteGraph n m :=
  pts.foldl (init := ∅) fun s ⟨x, y⟩ =>
    if hx : x < n then
      ⟨s.edges.set ⟨x, hx⟩ (s.edges[x] ||| BitVec.twoPow m y)⟩
    else
      s

end BipartiteGraph

structure BipartiteMap (n m n' m' : Nat) where
  xs : Vector (Fin n') n
  ys : Vector (Fin m') m

variable {n' m' : Nat}


namespace List

theorem foldlIdx_eq_foldl_enumFrom {α β} (xs : List α) (f : Nat → β → α → β) (init : β) (k : Nat) :
    foldlIdx f init xs k = foldl (fun acc ⟨i, x⟩ => f i acc x) init (xs.enumFrom k) := by
  induction xs generalizing init k with
  | nil => simp
  | cons x xs ih => simp [foldlIdx, foldl, ih]

/--
Sorts and deduplicates a list, using merge sort with the given comparison relation,
then splitting using the given equality relation,
returning along with each element the original indexes at which that element occurs.

It is characterized by the following properties:
- `xs.sortDedupWithIndexes.map (·.1) = xs.sortDedup`
- `(∃ l, i ∈ l ∧ (a, l) ∈ sortDedupWithIndexes xs) ↔ xs[i] = a`
-/
def sortDedupWithIndexes {α} (xs : List α)
    (le : α → α → Bool := by exact (· ≤ ·)) (eq : α → α → Bool := by exact (· = ·)) :
    List (α × List (Fin xs.length)) :=
  let enumSorted := xs.finEnum.mergeSort fun ⟨_, x⟩ ⟨_, y⟩ => le x y
  let splits := enumSorted.groupBy fun ⟨_, x⟩ ⟨_, y⟩ => eq x y
  splits.attach.map fun ⟨s, m⟩ => ((s.head (ne_nil_of_mem_groupBy m)).2, s.map (·.1))

variable {α} [LE α] [DecidableRel ((· : α) ≤ ·)] [DecidableEq α]
  {xs : List α} {le eq : α → α → Bool}

-- These next two claims presumably require additional hypotheses on the order.

proof_wanted map_fst_sortDedupWithIndexes :
    xs.sortDedupWithIndexes.map (·.1) = xs.mergeSort.eraseReps

proof_wanted sortDedupWithIndexes_iff {a : α} {i : Fin xs.length} :
    (∃ l, i ∈ l ∧ (a, l) ∈ sortDedupWithIndexes xs) ↔ xs[i] = a

end List

namespace BipartiteGraph

def dedupFst (g : BipartiteGraph n m) : Σ n', BipartiteGraph n' m × BipartiteMap n m n' m :=
  let sorted := g.edges.toList.enum.mergeSort fun ⟨i, x⟩ ⟨j, y⟩ => x ≤ y
  let split := sorted.toArray.groupByKey (·.2)
  sorry

def sortFst (g : BipartiteGraph n m) : BipartiteGraph n m × BipartiteMap n m n m := sorry

end BipartiteGraph

structure Cylinder (n m : Nat) where
  xs : BitVec n
  ys : BitVec m
deriving DecidableEq, Repr

namespace Cylinder

variable {n m : Nat}

def singleton (x : Fin n) (y : Fin m): Cylinder n m :=
  { xs := BitVec.twoPow n x, ys := BitVec.twoPow m y }

def toString (r : Cylinder n m) : String :=
  s!"{r.xs} × {r.ys}"

instance : ToString (Cylinder n m) where
  toString := toString

instance instPointMembership : Membership (Nat × Nat) (Cylinder n m) where
  mem r x := r.xs.getLsbD x.1 && r.ys.getLsbD x.2

instance (x : Nat × Nat) (r : Cylinder n m) : Decidable (x ∈ r) := by
  dsimp [Membership.mem]
  infer_instance

/--
We say `r₁ ≤ r₂` if and only if every point in `r₁` is contained in `r₂`.
-/
instance instLE : LE (Cylinder n m) where
  le r₁ r₂ := (r₁.xs ||| r₂.xs = r₂.xs) && (r₁.ys ||| r₂.ys = r₂.ys)

instance : DecidableRel ((· : Cylinder n m) ≤ ·) := by
  dsimp [LE.le, instLE]
  infer_instance

def subset (r : Cylinder n m) (s : BipartiteGraph n m) :=
  r.xs.all fun x => (s.edges[x] ||| r.ys) = s.edges[x]

def area (r : Cylinder n m) : Nat := r.xs.popCount * r.ys.popCount

end Cylinder

namespace Cylinder

def mapFst (f : Vector (Fin n') n) (r : Cylinder n' m) : Cylinder n m :=
  { xs := BitVec.ofFnLE fun x => r.xs[f[x]], ys := r.ys }

def mapSnd (f : Vector (Fin m') m) (r : Cylinder n m') : Cylinder n m :=
  { xs := r.xs, ys := BitVec.ofFnLE fun y => r.ys[f[y]] }

def map (f : BipartiteMap n m n' m') (r : Cylinder n' m') : Cylinder n m :=
  r.mapFst f.xs |>.mapSnd f.ys

end Cylinder


structure SortedBipartiteGraph (n n' m : Nat) where
  edges : Vector (BitVec m) n'
  lookup : Vector (BitVec n) n'

namespace BipartiteGraph

def sort (g : BipartiteGraph n m) : Σ n', SortedBipartiteGraph n n' m :=
  let presorted := g.edges.toList
    |>.mergeSort (fun x y =>
      let px := x.popCount
      let py := y.popCount
      px < py || (px = py && x < y))
    |>.eraseDups
  let sorted := Vector.mk (presorted.mergeSort fun x y => x ⊆ y).toArray rfl
  ⟨_,
    { edges := sorted
      -- We could compute this more efficiently by carrying around indices above.
      lookup := Vector.ofFn fun x' => BitVec.ofFnLE fun x => g.edges[x] == sorted[x'] }⟩

end BipartiteGraph





variable {n : Nat}

structure MaximalBicliqueState (n m : Nat) where
  candidates : BitVec n
  xs : BitVec n
  ys : BitVec m

def maximalBicliques' (g : BipartiteGraph n m) : List (Cylinder n m) :=
  let sorted := BipartiteGraph.sort g
  let r := go sorted.edges [] [⟨.allOnes _, 0, .allOnes _⟩]
  -- We still need to apply the lookup from sorted to each cylinder in r.
  sorry
where
  go (g : Vector (BitVec m) n) (maximal : List (Cylinder n m))
      (queue : List (MaximalBicliqueState n m)) : List (Cylinder n m) :=
    sorry
  maximals (g : Vector (BitVec m) n)


/-- Find all (inclusion-)maximal generalized rectangles contained within `xs`. -/
partial def maximalBicliques (pts : BipartiteGraph n n) : List (Cylinder n n) :=
  go [] [(n, Cylinder.mk 0 (.allOnes _))]
where
  go (maximal : List (Cylinder n n)) (queue : List (Nat × Cylinder n n)) :
    List (Cylinder n n) :=
  match queue with
  | [] => maximal
  | (k, r) :: rs =>
    let yss := (List.range k).filter (fun i => ! r.xs.getLsbD i)
      |>.map (fun i => pts.edges[i]!) |>.eraseDups
    let next := yss.filterMap fun ys =>
      let ys' := r.ys &&& ys
      if ys' = 0 then none else
        let xs' := BitVec.ofListNat n <| (List.range k).filter (fun i => ys ⊆ pts.edges[i]!)
        let k' := (List.range k).filter (fun i => ys = pts.edges[i]!) |>.min?.getD 0
        some (k', { xs := r.xs ||| xs', ys := ys' })
    if next.isEmpty then
      if maximal.any (r ≤ ·) then
        go maximal rs
      else
        -- dbgTrace s!"{r}" fun _ =>
        go (r :: maximal.filter (! · ≤ r)) rs
    else
      go maximal (next ++ rs)

/-
x x
xxx
xxx
-/
def board := BipartiteGraph.ofList 3 3 [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (2, 2)]

/-- info: [{ xs := 0x7#3, ys := 0x3#3 }, { xs := 0x5#3, ys := 0x7#3 }] -/
#guard_msgs in
#eval maximalBicliques board
