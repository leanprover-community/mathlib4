/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear map
-/

public section


open LinearMap Matrix Set Submodule Matrix

universe u v w

namespace Matrix

section CommSemiring

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type v} [CommSemiring R]

theorem proj_diagonal (i : n) (w : n → R) : proj i ∘ₗ (diagonal w).mulVecLin = w i • proj i :=
  LinearMap.ext fun _ => mulVec_diagonal _ _ _

theorem diagonal_comp_single (w : n → R) (i : n) :
    (diagonal w).mulVecLin ∘ₗ (LinearMap.single R (fun _ : n => R) i) =
      w i • LinearMap.single R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

theorem mulVecLin_diagonal (w : n → R) :
    (diagonal w).mulVecLin = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

@[deprecated mulVecLin_diagonal +typeChanged (since := "2026-11-25")]
theorem diagonal_toLin' (w : n → R) :
    toLin' (diagonal w) = LinearMap.pi fun i => w i • LinearMap.proj i :=
  mulVecLin_diagonal w

end CommSemiring

section Semifield

variable {m : Type*} [Fintype m] {K : Type u} [Semifield K]

theorem ker_mulVecLin_diagonal [DecidableEq m] (w : m → K) :
    ker (diagonal w).mulVecLin =
      ⨆ i ∈ { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  rw [← comap_bot]
  simpa [← ker_comp, proj_diagonal, ker_smul', ← iInf_ker_proj] using
    (iSup_range_single_eq_iInf_ker_proj K _ isCompl_compl {i | w i = 0}.toFinite).symm

@[deprecated ker_mulVecLin_diagonal +typeChanged (since := "2026-11-25")]
theorem ker_diagonal_toLin' [DecidableEq m] (w : m → K) :
    ker (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) :=
  ker_mulVecLin_diagonal w

theorem range_diagonal [DecidableEq m] (w : m → K) :
    LinearMap.range (diagonal w).mulVecLin =
      ⨆ i ∈ { i | w i ≠ 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  dsimp only [mem_ofPred_eq]
  rw [← Submodule.map_top, ← iSup_range_single, Submodule.map_iSup]
  congr; funext i
  rw [← LinearMap.range_comp, diagonal_comp_single, ← range_smul']

end Semifield

end Matrix

namespace LinearMap

section Field

variable {m : Type*} [Fintype m] {K : Type u} [Field K]

theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    LinearMap.rank (diagonal w).mulVecLin = Fintype.card { i // w i ≠ 0 } := by
  have hIJ : IsCompl { i : m | w i ≠ 0 } { i : m | w i = 0 } :=
    (isCompl_compl (x := {i : m | w i = 0})).symm
  have B₁ := iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) hIJ (Set.toFinite _)
  rw [LinearMap.rank, range_diagonal, B₁, ← @rank_fun' K]
  exact iInfKerProjEquiv K (fun _ ↦ K) hIJ.disjoint hIJ.codisjoint.top_le |>.rank_eq

end Field

end LinearMap
