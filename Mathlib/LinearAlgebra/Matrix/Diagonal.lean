/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension.LinearMap

#align_import linear_algebra.matrix.diagonal from "leanprover-community/mathlib"@"b1c23399f01266afe392a0d8f71f599a0dad4f7b"

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/


noncomputable section

open LinearMap Matrix Set Submodule Matrix

universe u v w

namespace Matrix

section CommSemiring -- Porting note: generalized from `CommRing`

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type v} [CommSemiring R]

theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun _ => mulVec_diagonal _ _ _
#align matrix.proj_diagonal Matrix.proj_diagonal

theorem diagonal_comp_stdBasis (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.stdBasis R (fun _ : n => R) i) =
      w i • LinearMap.stdBasis R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)
#align matrix.diagonal_comp_std_basis Matrix.diagonal_comp_stdBasis

theorem diagonal_toLin' (w : n → R) :
    toLin' (diagonal w) = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _
#align matrix.diagonal_to_lin' Matrix.diagonal_toLin'

end CommSemiring

section Semifield

variable {m n : Type*} [Fintype m] [Fintype n] {K : Type u} [Semifield K]

-- maybe try to relax the universe constraint
theorem ker_diagonal_toLin' [DecidableEq m] (w : m → K) :
    ker (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i = 0 }, LinearMap.range (LinearMap.stdBasis K (fun _ => K) i) := by
  rw [← comap_bot, ← iInf_ker_proj, comap_iInf]
  have := fun i : m => ker_comp (toLin' (diagonal w)) (proj i)
  simp only [comap_iInf, ← this, proj_diagonal, ker_smul']
  have : univ ⊆ { i : m | w i = 0 } ∪ { i : m | w i = 0 }ᶜ := by rw [Set.union_compl_self]
  exact (iSup_range_stdBasis_eq_iInf_ker_proj K (fun _ : m => K) disjoint_compl_right this
    (Set.toFinite _)).symm
#align matrix.ker_diagonal_to_lin' Matrix.ker_diagonal_toLin'

theorem range_diagonal [DecidableEq m] (w : m → K) :
    LinearMap.range (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i ≠ 0 }, LinearMap.range (LinearMap.stdBasis K (fun _ => K) i) := by
  dsimp only [mem_setOf_eq]
  rw [← Submodule.map_top, ← iSup_range_stdBasis, Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp, diagonal_comp_stdBasis, ← range_smul']
#align matrix.range_diagonal Matrix.range_diagonal

end Semifield

end Matrix

namespace LinearMap

section Field

variable {m n : Type*} [Fintype m] [Fintype n] {K : Type u} [Field K]

theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    LinearMap.rank (toLin' (diagonal w)) = Fintype.card { i // w i ≠ 0 } := by
  have hu : univ ⊆ { i : m | w i = 0 }ᶜ ∪ { i : m | w i = 0 } := by rw [Set.compl_union_self]
  have hd : Disjoint { i : m | w i ≠ 0 } { i : m | w i = 0 } := disjoint_compl_left
  have B₁ := iSup_range_stdBasis_eq_iInf_ker_proj K (fun _ : m => K) hd hu (Set.toFinite _)
  have B₂ := iInfKerProjEquiv K (fun _ ↦ K) hd hu
  rw [LinearMap.rank, range_diagonal, B₁, ← @rank_fun' K]
  apply LinearEquiv.rank_eq
  apply B₂
#align matrix.rank_diagonal LinearMap.rank_diagonal

end Field

end LinearMap
