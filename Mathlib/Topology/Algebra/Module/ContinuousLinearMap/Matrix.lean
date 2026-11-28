/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix

set_option doc.verso true
set_option doc.verso.suggestions false

/-! # Continuous linear maps and matrices

In this file we collect definitions and theorems about various maps for matrices as continuous
linear maps.

## Main definitions

* `Matrix.diagContinuousLinearMap`: `Matrix.diag` as a continuous linear map
* `Matrix.diagonalContinuousLinearMap`: `Matrix.diagonal` as a continuous linear map
* `Matrix.entryContinuousLinearMap`: evaluation of a matrix as a continuous linear map
* `Matrix.singleContinuousLinearMap`: `Matrix.single` as a continuous linear map

-/

@[expose] public section

namespace Matrix

variable {m n R M : Type*}
    [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

variable (n R M) in
/-- `Matrix.diag` as a continuous linear map. -/
@[simps!]
def diagContinuousLinearMap :
    (Matrix n n M) →L[R] n → M where
  __ := Matrix.diagLinearMap n R M
  cont := continuous_matrix_diag

@[norm_cast]
theorem coe_diagContinuousLinearMap :
    (diagContinuousLinearMap n R M : Matrix n n M → (n → M)) = diag := rfl

@[norm_cast, simp]
theorem toLinearMap_diagContinuousLinearMap :
    (diagContinuousLinearMap n R M).toLinearMap = diagLinearMap n R M :=
  rfl

section diagonal

variable [DecidableEq n]

variable (n R M) in
/-- `Matrix.diagonal` as a continuous linear map. -/
@[simps!]
def diagonalContinuousLinearMap :
    (n → M) →L[R] Matrix n n M where
  __ := Matrix.diagonalLinearMap n R M
  cont := continuous_id.matrix_diagonal

@[norm_cast]
theorem coe_diagonalContinuousLinearMap :
    (diagonalContinuousLinearMap n R M : (n → M) → Matrix n n M) = diagonal := rfl

@[norm_cast, simp]
theorem toLinearMap_diagonalContinuousLinearMap :
    (diagonalContinuousLinearMap n R M).toLinearMap = diagonalLinearMap n R M :=
  rfl

end diagonal

variable (R M) in
/-- Extracting entries from a matrix as a continuous linear map. -/
@[simps!]
def entryContinuousLinearMap (i : m) (j : n) :
    Matrix m n M →L[R] M where
  __ := entryLinearMap R M i j
  cont := continuous_id.matrix_elem _ _

@[norm_cast]
theorem coe_entryContinuousLinearMap (i : m) (j : n) :
    (entryContinuousLinearMap R M i j : Matrix m n M → M) = fun M ↦ M i j := rfl

@[norm_cast, simp]
theorem toLinearMap_entryContinuousLinearMap (i : m) (j : n) :
    (entryContinuousLinearMap R M i j).toLinearMap = entryLinearMap R M i j :=
  rfl

section single

variable [DecidableEq m] [DecidableEq n]

variable (R) in
/-- `Matrix.single` as a continuous linear map. -/
@[simps!]
def singleContinuousLinearMap (i : m) (j : n) :
    M →L[R] Matrix m n M where
  __ := singleLinearMap R i j
  cont := continuous_matrix_single M i j

@[norm_cast]
theorem coe_singleContinuousLinearMap (i : m) (j : n) :
    (singleContinuousLinearMap R i j : M → Matrix m n M) = single i j := rfl

@[norm_cast, simp]
theorem toLinearMap_singleContinuousLinearMap (i : m) (j : n) :
    (singleContinuousLinearMap R i j).toLinearMap = singleLinearMap R i j (α := M) :=
  rfl

end single

end Matrix
