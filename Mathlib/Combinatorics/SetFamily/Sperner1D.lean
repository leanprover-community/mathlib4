/-
Copyright (c) 2026 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic

/-!
# 1-Dimensional Sperner's Lemma

This module formalizes the 1-dimensional Sperner's Lemma.
In 1D, Sperner's Lemma essentially states that for a line segment divided into smaller segments,
if the vertices are colored with two colors (e.g., 0 and 1) such that the two
endpoints have different colors, then the number of segments whose endpoints
have different colors must be odd.

## Main declarations

* `sperner_1d` - The primary theorem for 1D Sperner's lemma.

## Implementation Notes

* **Boundary Semantics**: We model the coloring as a function `Fin (n + 1) → ZMod 2` rather
  than `ℕ → ZMod 2`. This exactly captures the `n + 1` vertices of a line segment divided into
  `n` sub-segments. It eliminates the need to carry around bound proofs (`i < n + 1`) or handle
  out-of-bounds evaluations, making invalid states unrepresentable at the type level.
* **Telescoping Sums in ZMod 2**: The core trick of the 1D Sperner's lemma is using `ZMod 2`
  addition. The sum of `edgeDiff c i = c i + c (i + 1)` over all segments telescopes to
  `c 0 + c n`. Because `x + x = 0` in `ZMod 2` (via `CharTwo.add_self_eq_zero`), every
  intermediate vertex is counted exactly twice and vanishes. This beautifully reduces a
  combinatorial parity counting problem into a simple algebraic sum, avoiding tedious parity
  case splits.
-/

@[expose] public section

namespace Sperner1D

open Finset

/-- A 1D Sperner coloring assigns a color (0 or 1 in ZMod 2) to each of the `n + 1` vertices. -/
def SpernerColoring (n : ℕ) := Fin (n + 1) → ZMod 2

/-- The difference between the colors of adjacent vertices `i` and `i + 1`. -/
def edgeDiff {n : ℕ} (c : SpernerColoring n) (i : Fin n) : ZMod 2 :=
  c (Fin.castSucc i) + c (Fin.succ i)

/-- The simplified formula for the edge difference. -/
@[simp]
lemma edgeDiff_apply {n : ℕ} (c : SpernerColoring n) (i : Fin n) :
    edgeDiff c i = c (Fin.castSucc i) + c (Fin.succ i) := rfl

/-- The sum of color differences over all segments. -/
def totalDiff {n : ℕ} (c : SpernerColoring n) : ZMod 2 :=
  ∑ i : Fin n, edgeDiff c i

/-- The core telescoping sum lemma: the sum of all segment differences equals the sum of
the endpoints (in ZMod 2). -/
lemma totalDiff_eq {n : ℕ} (c : SpernerColoring n) : totalDiff c = c 0 + c (Fin.last n) := by
  induction n with
  | zero =>
    simp only [totalDiff, univ_eq_empty, sum_empty]
    have h : (0 : Fin 1) = Fin.last 0 := rfl
    rw [h]
    exact (CharTwo.add_self_eq_zero _).symm
  | succ n ih =>
    have h1 : totalDiff c = (∑ i : Fin n, edgeDiff c (Fin.castSucc i)) +
        edgeDiff c (Fin.last n) := by
      dsimp only [totalDiff]
      rw [Fin.sum_univ_castSucc]
    let c_prev : SpernerColoring n := fun i => c (Fin.castSucc i)
    have h2 : (∑ i : Fin n, edgeDiff c (Fin.castSucc i)) = totalDiff c_prev := rfl
    rw [h1, h2, ih c_prev]
    dsimp only [c_prev, edgeDiff]
    have h_zero : c (Fin.castSucc 0) = c 0 := rfl
    have h_last : c (Fin.succ (Fin.last n)) = c (Fin.last (n + 1)) := rfl
    rw [h_zero, h_last]
    rw [← add_assoc, add_assoc (c 0), CharTwo.add_self_eq_zero, add_zero]

/-- If two colors are distinct, their sum in ZMod 2 is exactly 1. -/
lemma diff_color_eq_one {x y : ZMod 2} (h : x ≠ y) : x + y = 1 := by
  revert x y
  decide

/-- If the endpoints have different colors, the total difference is 1. -/
lemma sperner_1d_totalDiff {n : ℕ} (c : SpernerColoring n) (h : c 0 ≠ c (Fin.last n)) :
    totalDiff c = 1 := by
  rw [totalDiff_eq]
  exact diff_color_eq_one h

/-- The set of edges where the color changes. -/
def diffEdges {n : ℕ} (c : SpernerColoring n) : Finset (Fin n) :=
  univ.filter (fun i => edgeDiff c i = 1)

/-- An edge changes color if and only if its edge difference is 1. -/
@[simp]
lemma mem_diffEdges {n : ℕ} (c : SpernerColoring n) (i : Fin n) :
    i ∈ diffEdges c ↔ edgeDiff c i = 1 := by
  simp only [diffEdges, mem_filter, mem_univ, true_and]

/-- The total difference equals the number of color-changing edges modulo 2. -/
lemma totalDiff_eq_card_mod_two {n : ℕ} (c : SpernerColoring n) :
    totalDiff c = (diffEdges c).card := by
  rw [totalDiff, diffEdges]
  symm
  rw [← sum_boole]
  apply sum_congr rfl
  intro i _
  generalize edgeDiff c i = x
  revert x
  decide

/-- (k : ZMod 2) = 1 means k is odd. -/
lemma zmod2_eq_one_imp_odd {k : ℕ} (h : (k : ZMod 2) = 1) : Odd k := by
  rw [Nat.odd_iff, ← ZMod.val_natCast 2 k]
  exact congrArg ZMod.val h

/-- The 1D Sperner's Lemma: if the endpoints have different colors,
then the number of color-changing edges is odd. -/
theorem sperner_1d {n : ℕ} (c : SpernerColoring n) (h : c 0 ≠ c (Fin.last n)) :
    Odd (diffEdges c).card := by
  have h1 : totalDiff c = 1 := sperner_1d_totalDiff c h
  have h2 : totalDiff c = (diffEdges c).card := totalDiff_eq_card_mod_two c
  rw [h2] at h1
  exact zmod2_eq_one_imp_odd h1

end Sperner1D
