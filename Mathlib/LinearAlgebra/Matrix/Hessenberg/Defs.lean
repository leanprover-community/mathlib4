/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Upper Hessenberg matrices

A square matrix is upper Hessenberg when all entries below the subdiagonal are zero.

This file defines the predicate `Matrix.IsUpperHessenberg` with a corresponding `Decidable`
instance.

## Main definitions

- `Matrix.IsUpperHessenberg`

## Main results

- `Matrix.isUpperHessenberg_fin_iff`: the `IsUpperHessenberg` preducate on `Fin n`
- `Matrix.IsUpperTriangular.isUpperHessenberg`: upper triangular matrices are upper Hessenberg.
-/

public section

namespace Matrix

variable {R m : Type*} [Zero R] [Preorder m] [SuccOrder m]

/-- `M` is upper Hessenberg: entries strictly below the subdiagonal vanish. -/
abbrev IsUpperHessenberg (M : Matrix m m R) : Prop :=
  ∀ ⦃i j⦄, Order.succ j < i → M i j = 0

instance decidableIsUpperHessenberg [DecidableEq R] [Fintype m] [DecidableLT m]
    (M : Matrix m m R) : Decidable M.IsUpperHessenberg :=
  decidable_of_iff (∀ ij : m × m, Order.succ ij.2 < ij.1 → M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

theorem IsUpperTriangular.isUpperHessenberg {M : Matrix m m R} (h : M.IsUpperTriangular) :
    M.IsUpperHessenberg :=
  fun _ j hij => h ((Order.le_succ j).trans_lt hij)

theorem isUpperHessenberg_fin_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) R} :
    M.IsUpperHessenberg ↔ ∀ i j : Fin n, (j : ℕ) + 1 < i → M i j = 0 := by
  simp only [IsUpperHessenberg, Fin.orderSucc_lt_iff]

end Matrix

end
