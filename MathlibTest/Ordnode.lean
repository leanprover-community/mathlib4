module

meta import Mathlib.Data.Ordmap.Invariants

/-!
# Tests for the operations on `Ordnode`

`Mathlib/Data/Ordmap/Invariants.lean` and `Mathlib/Data/Ordmap/Ordset.lean` verify only some of
the operations on `Ordnode`. Several of the others are compared here with operations on lists, on
small inputs, and each result must be a balanced tree with the right cached sizes.

`insertMin`, `insertMax`, `link`, `take`, `drop`, `splitAt`, `filter` and `partition` never
compare elements, so they are tested on one list of each length (`filter` and `partition` with
every predicate on its elements).
-/

open Ordnode

/-- The cached sizes of a tree are right and the tree is balanced: `Ordnode.Sized` and
`Ordnode.Balanced`, as a `Bool`. -/
meta def wellFormed {α : Type} : Ordnode α → Bool
  | nil => true
  | node s l _ r =>
    s == l.size + r.size + 1 && decide (BalancedSz l.size r.size) && wellFormed l && wellFormed r

/-- The tree `t` is well formed and its elements are those of `l`, in order. -/
meta def agrees {α : Type} [BEq α] (t : Ordnode α) (l : List α) : Bool :=
  wellFormed t && t.toList == l

/-- Equality of trees, cached sizes included, as a `Bool`. -/
meta def same : Ordnode ℕ → Ordnode ℕ → Bool
  | nil, nil => true
  | node m l x r, node n l' y r' => m == n && x == y && same l l' && same r r'
  | _, _ => false

/-- The trees `ofList a`, `ofList a.reverse` and `ofAscList a`, without repeats, for a strictly
increasing list `a`. -/
meta def trees (a : List ℕ) : List (Ordnode ℕ) :=
  [ofList a, ofList a.reverse, ofAscList a].pwFilter (!same · ·)

-- `ofList`, `ofAscList` and `ofList'`
#guard (List.range 8).sublists.all fun a ↦ (trees a).all (agrees · a)
#guard ((List.range 70).map List.range).all fun l ↦ agrees (ofAscList l) l && agrees (ofList' l) l
#guard agrees (ofList' [1, 1, 2, 2]) [1, 2] && agrees (ofList' [2, 1, 2, 0, 1]) [0, 1, 2]

-- `insertMin x t` is `x :: t` and `insertMax t x` is `t ++ [x]`
#guard agrees ((List.range 8).foldr insertMin nil) (List.range 8)
#guard agrees ((List.range 8).foldl insertMax nil) (List.range 8)
#guard ((List.range 9).map (List.range' 1)).all fun a ↦ (trees a).all fun t ↦
  agrees (insertMin 0 t) (0 :: a) && agrees (insertMax t 9) (a ++ [9])

-- the verified operations work on a tree made by `insertMin`
#guard agrees (erase 7 (insertMin 1 (insertMin 2 (ofList [7, 3, 6, 4, 5])))) [1, 2, 3, 4, 5, 6]

-- `powerset`: the subsets, in lexicographic order
#guard ((List.range 8).map List.range).all fun l ↦
  let p := powerset (ofList l)
  wellFormed p && p.toList.all wellFormed && p.toList.map toList == l.sublists.mergeSort

-- `link l x r` is `l ++ x :: r`
#guard (List.range 9).all fun m ↦ (List.range 9).all fun n ↦
  (trees (List.range m)).all fun l ↦ (trees (List.range' (m + 1) n)).all fun r ↦
    agrees (link l m r) (List.range (m + n + 1))

-- `take`, `drop` and `splitAt`
#guard ((List.range 9).map List.range).all fun a ↦ (trees a).all fun t ↦ (List.range 9).all fun i ↦
  agrees (take i t) (a.take i) && agrees (drop i t) (a.drop i) &&
    agrees (splitAt i t).1 (a.take i) && agrees (splitAt i t).2 (a.drop i)

-- `splitAtAux` is `takeAux` and `dropAux` in one pass, on every tree and every index
example {α : Type*} (t : Ordnode α) (i : ℕ) : splitAtAux t i = (takeAux t i, dropAux t i) := by
  induction t generalizing i with
  | nil => rfl
  | node _ l _ r ihl ihr =>
    rw [splitAtAux, takeAux, dropAux]
    by_cases h : i = 0
    · simp [h]
    · rcases Nat.psub' i l.size with _ | _ | j <;> simp [h, ihl, ihr]

-- `filter`, `partition` and `split`
#guard ((List.range 10).map List.range).all fun a ↦ (trees a).all fun t ↦ a.sublists.all fun b ↦
  agrees (filter (· ∈ b) t) b && agrees (partition (· ∈ b) t).1 b &&
    agrees (partition (· ∈ b) t).2 (a.filter (· ∉ b))
#guard (List.range 8).sublists.all fun a ↦ (trees a).all fun t ↦ (List.range 9).all fun x ↦
  agrees (split x t).1 (a.filter (· < x)) && agrees (split x t).2 (a.filter (x < ·))

-- `union`, `diff`, `inter`, `isSubset` and `disjoint`
#guard (List.range 6).sublists.all fun a ↦ (List.range 6).sublists.all fun b ↦
  (trees a).all fun s ↦ (trees b).all fun t ↦
    agrees (union s t) (a ∪ b).mergeSort && agrees (diff s t) (a.removeAll b) &&
      agrees (inter s t) (a ∩ b) && isSubset s t == decide (a ⊆ b) && disjoint s t == a.all (· ∉ b)

-- `union` and `inter` keep the elements of the first set
#guard
  letI : LE (ℕ × ℕ) := ⟨fun a b ↦ a.1 ≤ b.1⟩
  (List.range 4).sublists.all fun a ↦ (List.range 4).sublists.all fun b ↦
    let s := ofList (a.map (·, 1))
    let t := ofList (b.map (·, 2))
    agrees (inter s t) ((a ∩ b).map (·, 1)) &&
      agrees (union s t) ((a ∪ b).mergeSort.map fun x ↦ (x, if x ∈ a then 1 else 2))
