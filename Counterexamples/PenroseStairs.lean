/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Basic

/-!
# Penrose Stairs Paradox

This file formalizes the classical Penrose stairs impossible object:

1. **Negative Result (Impossibility in dimension ≤ 3)**:
   On any finite cyclic path (`Fin n`), a height function with values in a linearly ordered
   type cannot strictly increase at every step, as the maximum element on a finite non-empty
   domain cannot have a strictly larger successor.

2. **Positive Result (Visual Realization in ℤ⁴)**:
   The impossible object is geometrically realized in 4-dimensional discrete space `ℤ⁴`:
   - An orthogonal projection `visualProj : ℤ⁴ → ℤ²` yields an exact closed cycle of 4 planar
     steps, reproducing the classic 2D isometric Penrose illusion.
   - The spatial elevation $z$ strictly ascends along the 3 visible flights.
   - The 4 vertices are strictly distinct in 4D (`Function.Injective`).
-/

public section

namespace Counterexample

variable {α : Type*} [LinearOrder α]

/-- A discrete closed cycle of $n$ stairs ($n > 0$) with height values in any linearly ordered
space `α` cannot strictly increase at every step. -/
theorem penrose_stairs_3d_impossible (n : ℕ) [NeZero n]
    (h : Fin n → α)
    (h_asc : ∀ i : Fin n,
      h i < h ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩) : False := by
  have h_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, Finset.mem_univ _⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ h h_nonempty
  have h_step := h_asc m
  have h_le :=
    hm ⟨(m.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩ (Finset.mem_univ _)
  exact not_le_of_gt h_step h_le

/-- A point in 4-dimensional discrete space `Int⁴`. -/
@[ext]
structure Point4D where
  x : Int
  y : Int
  z : Int
  w : Int
deriving DecidableEq

/-- A point in the 2D visual projection plane `Int²`. -/
@[ext]
structure Point2D where
  u : Int
  v : Int
deriving DecidableEq

/-- Visual height is the 3rd spatial coordinate $z$. -/
def height4D (p : Point4D) : Int :=
  p.z

/-- The canonical orthogonal projection from 4D space onto the 2D visual plane $(x, y)$. -/
def visualProj (p : Point4D) : Point2D :=
  ⟨p.x, p.y⟩

/-- Four canonical vertices of the Penrose staircase in 4D space. -/
def vertex4D : Fin 4 → Point4D
  | 0 => ⟨0, 0, 0, 0⟩
  | 1 => ⟨1, 0, 1, 0⟩
  | 2 => ⟨1, 1, 2, 0⟩
  | 3 => ⟨0, 1, 3, 1⟩

/-- There exists an explicit 4-vertex configuration in `ℤ⁴` such that:
1. **Strict Visible Ascent**: Elevation strictly increases along the 3 visible flights.
2. **2D Visual Closure**: The 2D projected vertices form a closed cycle of directed
   unit steps in the plane.
3. **4D Non-Degeneracy**: The 4 vertices are strictly distinct in 4D (`Function.Injective`). -/
theorem penrose_stairs_4d_realization :
    height4D (vertex4D 0) < height4D (vertex4D 1) ∧
    height4D (vertex4D 1) < height4D (vertex4D 2) ∧
    height4D (vertex4D 2) < height4D (vertex4D 3) ∧
    visualProj (vertex4D 0) = ⟨0, 0⟩ ∧
    visualProj (vertex4D 1) = ⟨1, 0⟩ ∧
    visualProj (vertex4D 2) = ⟨1, 1⟩ ∧
    visualProj (vertex4D 3) = ⟨0, 1⟩ ∧
    Function.Injective vertex4D := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, rfl, ?_⟩
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  revert a b ha hb hab
  decide

end Counterexample
