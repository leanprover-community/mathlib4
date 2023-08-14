import Mathlib.Data.MLList.BestFirst
import Mathlib.Data.Nat.Sqrt

/-!
# Testing best first search and beam search.

We check that `bestFirstSearch` can find its way around a wall.
-/

open Lean MLList

def wall : Int × Int → Bool :=
  fun ⟨x, y⟩ => x ≤ 3 || y ≤ 3 || x ≥ 20 || y ≥ 20 || (x ≥ 6 && y ≥ 6)

def nbhd : Int × Int → MLList MetaM (Int × Int) :=
  fun ⟨x, y⟩ => MLList.ofList
      ([(x+1,y), (x-1,y), (x,y+1), (x,y-1)].filter wall)

instance : Ord (Int × Int) where
  compare p q :=
    let rp := p.1^2 + p.2^2
    let rq := q.1^2 + q.2^2
    if rp < rq then .lt
    else if rq < rp then .gt
    else if p.1 < q.1 then .lt
    else if q.1 < p.1 then .gt
    else if p.2 < q.2 then .lt
    else if q.2 < p.2 then .gt
    else .eq

#eval bestFirstSearch nbhd (10, 10) (maxQueued := some 4) |>.takeUpToFirst (· = (0,0)) |>.force
