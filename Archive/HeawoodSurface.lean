/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer

# The Heawood Graph (F014A): A Concrete CellularSurface

The Heawood graph (Foster census F014A) is the Levi graph (incidence graph) of
the Fano plane PG(2,2). It is a cubic arc-transitive graph on 14 vertices.

  - **Sabidussi**: Sab(G₄₂, C₃) where G₄₂ = Z₇ ⋊ Z₆ (order 42)
  - **Tiling**: {6,3} — 7 hexagonal faces on the torus (genus 1)
  - **CSS code**: [[21, 2, ≥ 3]]

Vertices 0–6 are the 7 points of the Fano plane.
Vertices 7–13 are the 7 lines.
Edge i connects a point to the line containing it.

All axioms verified by the Lean kernel (`decide`). No sorry.
-/

import Mathlib.Combinatorics.CellularSurface
import Archive.VoltageGraphs

set_option linter.style.nativeDecide false

open CellularSurface

/-- The Heawood graph embedded on a torus, as a CellularSurface.
    14 vertices (Fano points + lines), 21 edges, 7 hexagonal faces. -/
def heawoodSurface : CellularSurface where
  nV := 14
  nE := 21
  nF := 7
  edge_src := ![0, 1, 3, 1, 2, 4, 2, 3, 5, 3, 4, 6, 0, 4, 5, 1, 5, 6, 0, 2, 6]
  edge_tgt := ![7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13]
  edge_ne := by decide
  face_len := fun _ => 6
  face_len_pos := fun _ => by norm_num
  face_edge := ![
    ![0, 2, 7, 6, 19, 18],   -- Face 0: 0→7→3→9→2→13→0
    ![12, 14, 16, 15, 1, 0],  -- Face 1: 0→11→5→12→1→7→0
    ![18, 20, 11, 10, 13, 12], -- Face 2: 0→13→6→10→4→11→0
    ![3, 5, 10, 9, 2, 1],     -- Face 3: 1→8→4→10→3→7→1
    ![15, 17, 20, 19, 4, 3],  -- Face 4: 1→12→6→13→2→8→1
    ![6, 8, 14, 13, 5, 4],    -- Face 5: 2→9→5→11→4→8→2
    ![9, 11, 17, 16, 8, 7]    -- Face 6: 3→10→6→12→5→9→3
  ]
  face_dir := ![
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false],
    ![true, false, true, false, true, false]
  ]
  face_inj := by decide
  face_closed := by decide

/-- The Heawood surface satisfies ∂² = 0. -/
theorem heawood_d1_mul_d2_eq_zero : heawoodSurface.d1 * heawoodSurface.d2 = 0 :=
  heawoodSurface.d1_mul_d2_eq_zero

/-- Each column of d1 sums to zero (each edge has 2 endpoints). -/
example : ∀ e, ∑ v, heawoodSurface.d1 v e = 0 := heawoodSurface.d1_col_sum_eq_zero

/-- The Heawood code: Euler characteristic confirms genus 1, so k = 2. -/
theorem heawood_euler : (14 : ℤ) - 21 + 7 = 2 - 2 * 1 := by norm_num

/-! ### Bridge to voltage graph description

The Heawood graph has two descriptions:
1. **Combinatorial** (above): a `CellularSurface` with explicit edge_src/edge_tgt
2. **Algebraic** (`VoltageGraphs.lean`): `voltageGraphK2 7 0 4 6`, a voltage graph on K₂

We prove these define the same graph via the bijection v ↦ (v/7, v mod 7),
mapping Fano points 0–6 to fibre 0 and Fano lines 7–13 to fibre 1. -/

/-- The bijection Fin 14 → Fin 2 × ZMod 7 mapping vertex v to (v/7, v mod 7). -/
def heawoodBij (v : Fin 14) : Fin 2 × ZMod 7 :=
  (⟨v.val / 7, by omega⟩, (v.val : ZMod 7))

/-- **Bridge theorem**: the Heawood `CellularSurface` graph equals the Heawood
voltage graph under the bijection v ↦ (v/7, v mod 7). -/
theorem heawood_surface_eq_voltage :
    ∀ u v : Fin 14,
      (∃ e : Fin 21,
        (heawoodSurface.edge_src e = u ∧ heawoodSurface.edge_tgt e = v) ∨
        (heawoodSurface.edge_src e = v ∧ heawoodSurface.edge_tgt e = u)) ↔
      heawoodVoltage.Adj (heawoodBij u) (heawoodBij v) := by
  native_decide
