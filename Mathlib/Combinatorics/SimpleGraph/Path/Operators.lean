/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Transport and position on a finite path

Normalized adjacency and centered diagonal position on `SimpleGraph.pathGraph`.
-/

@[expose] public section

namespace SimpleGraph.pathGraph

open SimpleGraph

/-- The complex adjacency matrix of the canonical finite path. -/
noncomputable def adjacency (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := by
  classical
  exact (SimpleGraph.pathGraph d).adjMatrix ℂ

@[simp]
theorem adjacency_apply {d : ℕ} (i j : Fin d) :
    adjacency d i j = if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  simp only [adjacency, SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj]

/-- The largest adjacency eigenvalue, used to normalize transport. -/
noncomputable def spectralBound (d : ℕ) : ℝ :=
  2 * Real.cos (Real.pi / ((d : ℝ) + 1))

/-- Adjacency divided by its largest eigenvalue. -/
noncomputable def transport (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => adjacency d i j / (spectralBound d : ℂ)

/-- Equally spaced coordinates centered at zero. -/
noncomputable def positionCoordinate (d : ℕ) (j : Fin d) : ℝ :=
  (2 * ((j.val : ℝ) + 1) - ((d : ℝ) + 1)) / ((d : ℝ) - 1)

/-- The diagonal matrix of centered position coordinates. -/
noncomputable def position (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = j then (positionCoordinate d i : ℂ) else 0

theorem transport_eq_zero_of_not_adj {d : ℕ} {i j : Fin d}
    (h : ¬ (SimpleGraph.pathGraph d).Adj i j) : transport d i j = 0 := by
  simp only [SimpleGraph.pathGraph_adj] at h
  simp [transport, h]

theorem position_apply_of_ne {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    position d i j = 0 := by
  simp [position, hij]

theorem position_apply_self {d : ℕ} (i : Fin d) :
    position d i i = (positionCoordinate d i : ℂ) := by
  simp [position]

end SimpleGraph.pathGraph
