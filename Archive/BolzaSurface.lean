/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.CellularSurface
import Archive.VoltageGraphs

/-!
# The Bolza Surface: Möbius-Kantor Graph (F016A) on Genus 2

The Möbius-Kantor graph (Foster census F016A) = generalized Petersen graph
GP(8,3). It is a cubic arc-transitive graph on 16 vertices.

* **Sabidussi**: Sab(GL(2,3), C₃), |GL(2,3)| = 48
* **Voltage graph**: `voltageGraphK2 8 0 1 3` on K₂ with Z₈
* **Tiling**: {8,3} — 6 octagonal faces on the Bolza surface (genus 2)
* **CSS code**: [[24, 4, ≥ 6]]
* [Visualization](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/mobius-kantor-F016A.jpg)

All axioms verified by the Lean kernel (`decide`). No sorry.
-/

open CellularSurface

/-- The Möbius-Kantor graph GP(8,3) embedded on the Bolza surface (genus 2).
    16 vertices, 24 edges, 6 octagonal faces. -/
def bolzaSurface : CellularSurface where
  nV := 16
  nE := 24
  nF := 6
  -- Edges 0–7: outer ring, 8–15: inner star, 16–23: spokes
  edge_src := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  edge_tgt := ![1, 2, 3, 4, 5, 6, 7, 0, 11, 12, 13, 14, 15, 8, 9, 10, 8, 9, 10, 11, 12, 13, 14, 15]
  edge_ne := by decide
  face_len := fun _ => 8
  face_len_pos := fun _ => by norm_num
  face_edge := ![
    ![0, 17, 9, 20, 4, 21, 13, 16],   -- 0→1→9→12→4→5→13→8→0
    ![7, 6, 5, 4, 3, 2, 1, 0],         -- 0→7→6→5→4→3→2→1→0 (outer ring reversed)
    ![16, 8, 19, 3, 20, 12, 23, 7],   -- 0→8→11→3→4→12→15→7→0
    ![1, 18, 10, 21, 5, 22, 14, 17],  -- 1→2→10→13→5→6→14→9→1
    ![2, 19, 11, 22, 6, 23, 15, 18],  -- 2→3→11→14→6→7→15→10→2
    ![13, 10, 15, 12, 9, 14, 11, 8]   -- inner star reversed
  ]
  face_dir := ![
    ![true, true, true, false, true, true, true, false],
    ![false, false, false, false, false, false, false, false],
    ![true, true, false, true, true, true, false, true],
    ![true, true, true, false, true, true, true, false],
    ![true, true, true, false, true, true, true, false],
    ![false, false, false, false, false, false, false, false]
  ]
  face_inj := by decide
  face_closed := by decide

/-- The Bolza surface satisfies ∂² = 0. -/
theorem bolza_d1_mul_d2_eq_zero : bolzaSurface.d1 * bolzaSurface.d2 = 0 :=
  bolzaSurface.d1_mul_d2_eq_zero

/-- Euler characteristic confirms genus 2. -/
theorem bolza_euler : (16 : ℤ) - 24 + 6 = 2 - 2 * 2 := by norm_num

/-! ### Bridge to voltage graph description

The Bolza surface 1-skeleton is the Möbius-Kantor graph, which also has a
voltage graph description: `voltageGraphK2 8 0 1 3` (see `VoltageGraphs.lean`).
We prove these define the same graph via a GAP-computed bijection. -/

private def bolzaBijData : Array (Fin 2 × ZMod 8) := #[
  (0,0),(1,1),(0,1),(1,4),(0,4),(1,5),(0,5),(1,0),
  (1,3),(0,6),(1,2),(0,3),(1,7),(0,2),(1,6),(0,7)]
private theorem bolzaBijData_size : bolzaBijData.size = 16 := by native_decide

/-- The bijection `Fin 16 → Fin 2 × ZMod 8` making the Bolza surface graph
isomorphic to the Möbius-Kantor voltage graph. -/
def bolzaBij (v : Fin 16) : Fin 2 × ZMod 8 :=
  bolzaBijData[v.val]'(by have := bolzaBijData_size; omega)

/-- **Bridge theorem**: the Bolza `CellularSurface` graph equals the
Möbius-Kantor voltage graph under `bolzaBij`. -/
theorem bolza_surface_eq_voltage :
    ∀ u v : Fin 16,
      (∃ e : Fin 24,
        (bolzaSurface.edge_src e = u ∧ bolzaSurface.edge_tgt e = v) ∨
        (bolzaSurface.edge_src e = v ∧ bolzaSurface.edge_tgt e = u)) ↔
      mobiusKantorVoltage.Adj (bolzaBij u) (bolzaBij v) := by
  native_decide
