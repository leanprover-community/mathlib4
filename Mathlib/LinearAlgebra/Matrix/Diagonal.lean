/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.diagonal
! leanprover-community/mathlib commit b1c23399f01266afe392a0d8f71f599a0dad4f7b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.FreeModule.Rank

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

namespace Matrix

section CommRing

variable {n : Type _} [Fintype n] [DecidableEq n] {R : Type v} [CommRing R]

theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun j => mulVec_diagonal _ _ _
#align matrix.proj_diagonal Matrix.proj_diagonal

theorem diagonal_comp_stdBasis (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.stdBasis R (fun _ : n => R) i) =
      w i • LinearMap.stdBasis R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)
#align matrix.diagonal_comp_std_basis Matrix.diagonal_comp_stdBasis

theorem diagonal_toLin' (w : n → R) :
    (diagonal w).toLin' = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun v => funext fun i => mulVec_diagonal _ _ _
#align matrix.diagonal_to_lin' Matrix.diagonal_toLin'

end CommRing

section Field

variable {m n : Type _} [Fintype m] [Fintype n]

variable {K : Type u} [Field K]

-- maybe try to relax the universe constraint
theorem ker_diagonal_toLin' [DecidableEq m] (w : m → K) :
    ker (diagonal w).toLin' = ⨆ i ∈ { i | w i = 0 }, range (LinearMap.stdBasis K (fun i => K) i) :=
  by
  rw [← comap_bot, ← infi_ker_proj, comap_infi]
  have := fun i : m => ker_comp (to_lin' (diagonal w)) (proj i)
  simp only [comap_infi, ← this, proj_diagonal, ker_smul']
  have : univ ⊆ { i : m | w i = 0 } ∪ { i : m | w i = 0 }ᶜ := by rw [Set.union_compl_self]
  exact
    (supr_range_std_basis_eq_infi_ker_proj K (fun i : m => K) disjoint_compl_right this
        (Set.toFinite _)).symm
#align matrix.ker_diagonal_to_lin' Matrix.ker_diagonal_toLin'

theorem range_diagonal [DecidableEq m] (w : m → K) :
    (diagonal w).toLin'.range =
      ⨆ i ∈ { i | w i ≠ 0 }, (LinearMap.stdBasis K (fun i => K) i).range :=
  by
  dsimp only [mem_set_of_eq]
  rw [← Submodule.map_top, ← supr_range_std_basis, Submodule.map_supᵢ]
  congr ; funext i
  rw [← LinearMap.range_comp, diagonal_comp_std_basis, ← range_smul']
#align matrix.range_diagonal Matrix.range_diagonal

theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    rank (diagonal w).toLin' = Fintype.card { i // w i ≠ 0 } :=
  by
  have hu : univ ⊆ { i : m | w i = 0 }ᶜ ∪ { i : m | w i = 0 } := by rw [Set.compl_union_self]
  have hd : Disjoint { i : m | w i ≠ 0 } { i : m | w i = 0 } := disjoint_compl_left
  have B₁ := supr_range_std_basis_eq_infi_ker_proj K (fun i : m => K) hd hu (Set.toFinite _)
  have B₂ := @infi_ker_proj_equiv K _ _ (fun i : m => K) _ _ _ _ (by simp <;> infer_instance) hd hu
  rw [rank, range_diagonal, B₁, ← @rank_fun' K]
  apply LinearEquiv.rank_eq
  apply B₂
#align matrix.rank_diagonal Matrix.rank_diagonal

end Field

end Matrix

