/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.ToSet

/-!
# Binary splitting of represented sets

This file defines a binary splitting specification and its correctness theorem.
-/

@[expose] public section

namespace Inclusion.Cover

/-- Map `F` over the pieces produced by applying `split` to depth `n`, coarsening the results.
A value of `none` stops splitting. -/
def binarySplitMap {Iα Iβ β : Type*} [ToSet Iβ β] [Coarsen Iβ β]
    (split : Iα → Option (Iα × Iα)) : ℕ → Iα → (Iα → Iβ) → Iβ
  | 0, I, F => F I
  | n + 1, I, F =>
      match split I with
      | none => F I
      | some (J, K) =>
          Coarsen.coarsen β (binarySplitMap split n J F) (binarySplitMap split n K F)

theorem mem_binarySplitMap {Iα α Iβ β : Type*} [ToSet Iα α] [ToSet Iβ β] [Coarsen Iβ β]
    (split : Iα → Option (Iα × Iα))
    (hsplit : ∀ {I J K : Iα} {x : α}, split I = some (J, K) → x ∈ I → x ∈ J ∨ x ∈ K)
    (n : ℕ) {I : Iα} {F : Iα → Iβ} {x : α} {y : β}
    (hx : x ∈ I) (hy : ∀ J, x ∈ J → y ∈ F J) : y ∈ binarySplitMap split n I F := by
  induction n generalizing I with
  | zero => exact hy I hx
  | succ n ih =>
    rw [binarySplitMap]
    split
    · exact hy _ hx
    · rename_i J K h
      rcases hsplit h hx with hx | hx
      · exact Coarsen.mem_coarsen_left (ih hx)
      · exact Coarsen.mem_coarsen_right (ih hx)

end Inclusion.Cover
