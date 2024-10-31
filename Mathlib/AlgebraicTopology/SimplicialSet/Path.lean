/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Paths in simplicial sets

A path in a simplicial set `X` of length `n` is a directed path comprised of `n + 1` 0-simplices
and `n` 1-simplices, together with identifications between 0-simplices and the sources and targets
of the 1-simplices.

An `n`-simplex has a maximal path, the `spine` of the simplex, which is a path of length `n`.
-/

universe v u

namespace SSet

open CategoryTheory

open Simplicial SimplexCategory

variable (X : SSet.{u})

/-- A path in a simplicial set `X` of length `n` is a directed path of `n` edges.-/
@[ext]
structure Path (n : ℕ) where
  /-- A path includes the data of `n+1` 0-simplices in `X`.-/
  vertex (i : Fin (n + 1)) : X _[0]
  /-- A path includes the data of `n` 1-simplices in `X`.-/
  arrow (i : Fin n) : X _[1]
  /-- The sources of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_src (i : Fin n) : X.δ 1 (arrow i) = vertex i.castSucc
  /-- The targets of the 1-simplices in a path are identified with appropriate 0-simplices.-/
  arrow_tgt (i : Fin n) : X.δ 0 (arrow i) = vertex i.succ


variable {X} in
/-- For `j ≤ k ≤ n`, a path of length `n` restricts to a path of length `k-j`, namely the subpath
spanned by the vertices `j ≤ i ≤ k` and edges `j ≤ i < k`. -/
def Path.interval {n : ℕ} (f : Path X n) (j l : ℕ) (hjl : j + l < n + 1) :
    Path X l where
  vertex i := f.vertex (Fin.addNat i j)
  arrow i := f.arrow ⟨Fin.addNat i j, (by omega)⟩
  arrow_src i := by
    rw [f.arrow_src ⟨Fin.addNat i j, (by omega)⟩]
    congr
    refine Fin.eq_of_val_eq (Nat.mod_eq_of_lt ?_).symm
    omega
  arrow_tgt i := by
    have eq := f.arrow_tgt ⟨Fin.addNat i j, (by omega)⟩
    simp_rw [eq]
    congr 1
    apply Fin.eq_of_val_eq
    simp only [Fin.coe_addNat, Fin.succ_mk, Fin.val_succ, Fin.val_natCast]
    have : i.1 + 1 + j < n + 1 := by omega
    have : (i.1 + 1 + j) % (n + 1) = i.1 + 1 + j := by exact Nat.mod_eq_of_lt this
    rw [this, Nat.add_right_comm]

/-- The spine of an `n`-simplex in `X` is the path of edges of length `n` formed by
traversing through its vertices in order.-/
@[simps]
def spine (n : ℕ) (Δ : X _[n]) : X.Path n where
  vertex i := X.map (SimplexCategory.const [0] [n] i).op Δ
  arrow i := X.map (SimplexCategory.mkOfSucc i).op Δ
  arrow_src i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.δ_one_mkOfSucc]
    simp only [len_mk, Fin.coe_castSucc, Fin.coe_eq_castSucc]
  arrow_tgt i := by
    dsimp [SimplicialObject.δ]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.δ_zero_mkOfSucc]



end SSet
