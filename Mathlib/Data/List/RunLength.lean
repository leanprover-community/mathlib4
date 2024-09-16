/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.GroupBy
import Mathlib.Order.TypeTags

/-!
# Run-length encoding
-/

variable {α : Type*} [DecidableEq α]

namespace List

/-- Run-length encoding of a list. Returns a list of pairs `(n, a)` representing consecutive groups
of `a` of length `n`. -/
def RunLength (l : List α) : List (ℕ+ × α) :=
  ((l.groupBy (· == ·)).attachWith _ (fun _ ↦ ne_nil_of_mem_groupBy _)).map
    fun m ↦ (⟨m.1.length, length_pos_of_ne_nil m.2⟩, m.1.head m.2)

@[simp]
theorem runLength_nil : RunLength ([] : List α) = [] :=
  rfl

@[simp]
theorem runLength_replicate {n : ℕ} (hn : 0 < n) (a : α) :
    RunLength (replicate n a) = [(⟨n, hn⟩, a)] := by
  

def runLengthRecOn (l : List α) {p : List α → Sort*} (pn : p [])
    (pr : ∀ (n : ℕ+) a, p (replicate n a))

#exit
theorem join_map_runLength (l : List α) :
    (l.RunLength.map (fun x ↦ replicate x.1 x.2)).join = l := by
  convert join_groupBy (· == ·) l
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [map_cons]


end List
