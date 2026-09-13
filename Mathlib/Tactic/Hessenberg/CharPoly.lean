/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs
public import Mathlib.Tactic.Hessenberg.Recurrence
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of the Hessenberg characteristic polynomial recurrence

## Main results

`charpoly_eq_hessCharPoly`: the recurrence `Mathlib.Tactic.Hessenberg.hessCharPoly` computes the
characteristic polynomial of an upper Hessenberg matrix.

## Implementation details

The derivation of the recurrence formula for an `n x n` upper Hessenberg matrix `H` follows by
Laplace expansion of the determinant of the characteristic matrix, `CH`, for `H` along its last
column.

The minor `Hᵢ` of `CH` that omits the last column and the `i`th row of `H` has the following
structure:

```
  columns 0 ... i-1 of H       columns i ... n-2 of H
[             Mᵢ           |              *            ]   rows 0 ... i-1 of H
[             0            |              Tᵢ           ]   rows i+1 ... n-1 of H
```

where `Mᵢ` is the leading principal `i × i` minor of `CH` (and so is upper Hessenberg) and `Tᵢ` is a
`n-1-i × n-1-i` upper triangular matrix. Therefore

```
det Hᵢ = det Mᵢ · CH[i+1][i] · CH[i+2][i+1] · ... · CH[n-1][n-2]
```

and expanding `det CH` along its last column gives:

```
det CH = ∑_{i=0}^{n-1} (-1)^(i+n-1) CH[i][n-1] det Hᵢ
```

Now let `pₖ` be the characteristic polynomial of `Hₖ`, it is equal to `det CHₖ` where `CHₖ` is the
leading principal `k × k` minor of `CH`. In particular `pₙ = det CH` is the characteristic
polynomial of `H`.

By definition, we know that `CH[n-1][n-1] = X - H[n-1][n-1]` and `H_{n-1} = CH_{n-1}` and so we can
rewrite `det CH` as:

```
pₙ = (X - H[n-1][n-1]) p_{n-1} + ∑_{i=0}^{n-2} (-1)^(i+n-1) CH[i][n-1] det Hᵢ
```

Now consider each term in the tail sum. We can expand `Hᵢ` into its block form, note that
`CH[i][n-1] = -H[i][n-1]`, and collect negative factors to obtain:

```
(-1)^(i+n-1) CH[i][n-1] det Hᵢ = -H[i][n-1] · pᵢ · ∏_{j=i}^{n-2} H[j+1][j]
```

The leading principal submatrices `Hᵢ` are also upper Hessenberg and so the same expansion applies
to `p₀, ..., p_{n-1}` and so we get the recurrence formula:

```
p_{k+1} = (X - H[k][k]) pₖ - ∑_{t=0}^{k-1} H[t][k] · pₜ · ∏_{j=t}^{k-1} H[j+1][j]
```

In the formalization:

`Matrix.leadingBlock` - Defines the leading principal submatrix.
`IsUpperHessenberg.charmatrix` and `charmatrix_leadingBlock` - Shows that `CH` is upper Hessenberg
  with `Mₖ` the characteristic matrix of `Hₖ`.
`det_lastColMinor` - The formula for `det Hᵢ`.
`det_eq_sum_of_isUpperHessenberg` - The expansion of `det Hᵢ` along its last column.
`charpoly_isUpperHessenberg` - Specializes the determinant to `CH`.
`hessP_eq_charpoly` - The proof of the recurrence formula.
-/

open Polynomial Finset

namespace Matrix

variable {α : Type*} {k m n : ℕ}

/-- The leading `k × k` block of an `n × n` matrix. -/
def leadingBlock (M : Matrix (Fin n) (Fin n) α) (h : k ≤ n) : Matrix (Fin k) (Fin k) α :=
  M.submatrix (Fin.castLE h) (Fin.castLE h)

@[simp]
theorem leadingBlock_apply (M : Matrix (Fin n) (Fin n) α) (h : k ≤ n) (i j : Fin k) :
    M.leadingBlock h i j = M (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem leadingBlock_leadingBlock (M : Matrix (Fin n) (Fin n) α) (hkm : k ≤ m) (hmn : m ≤ n) :
    (M.leadingBlock hmn).leadingBlock hkm = M.leadingBlock (hkm.trans hmn) := rfl

@[simp]
theorem leadingBlock_self (M : Matrix (Fin n) (Fin n) α) : M.leadingBlock le_rfl = M := rfl

/-- The minor `Hᵢ` formed from `M` by deleting the`i`th row and the last column. -/
abbrev lastColMinor (M : Matrix (Fin (n + 1)) (Fin (n + 1)) α) (i : Fin n) :
    Matrix (Fin n) (Fin n) α :=
  M.submatrix i.castSucc.succAbove Fin.castSucc

/-- The leading block `Mᵢ` formed from the first `i` rows and columns of `M.lastColMinor i` is equal
to the leading `i×i` block of `M`. -/
theorem toSquareBlockProp_lastColMinor (M : Matrix (Fin (n + 1)) (Fin (n + 1)) α) (i : Fin n) :
    ((M.lastColMinor i).toSquareBlockProp (· < i)).submatrix
      (Fin.castLEquiv i.isLt.le) (Fin.castLEquiv i.isLt.le) =
        M.leadingBlock i.castSucc.isLt.le := by
  have hrow (a : Fin i) :
      i.castSucc.succAbove (Fin.castLE i.isLt.le a) = (Fin.castLE i.isLt.le a).castSucc :=
    Fin.succAbove_castSucc_of_lt _ _ a.isLt
  ext a b
  simp [toSquareBlockProp_def, hrow]

/-- The block `Tᵢ` formed from the last `n-1-i` rows and columns of `M.lastColMinor i` is equal to
rows `[i+1 ... n-1]` and columns `[i ... n-2]` of `M`. -/
theorem toSquareBlockProp_lastColMinor_not_lt (M : Matrix (Fin (n + 1)) (Fin (n + 1)) α)
    (i : Fin n) : (M.lastColMinor i).toSquareBlockProp (¬ · < i) =
      of fun a b => M a.1.succ b.1.castSucc := by
  have hrow (a : {j : Fin n // ¬ j < i}) : i.castSucc.succAbove a = a.1.succ :=
    Fin.succAbove_castSucc_of_le _ _ (not_lt.mp a.2)
  ext a b
  simp [toSquareBlockProp_def, hrow]

theorem charmatrix_leadingBlock {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R)
    (h : k ≤ n) : (M.leadingBlock h).charmatrix = M.charmatrix.leadingBlock h := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem IsUpperHessenberg.leadingBlock [Zero α] {M : Matrix (Fin n) (Fin n) α}
    (hM : M.IsUpperHessenberg) (h : k ≤ n) : (M.leadingBlock h).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff] at hM ⊢
  intro _ _ hij
  exact hM (by simpa [Fin.orderSucc_lt_iff] using hij)

theorem IsUpperHessenberg.charmatrix {R : Type*} [CommRing R] {M : Matrix (Fin n) (Fin n) R}
    (hM : M.IsUpperHessenberg) : M.charmatrix.IsUpperHessenberg := by
  rw [isUpperHessenberg_iff] at hM ⊢
  intro _ j hij
  rw [charmatrix_apply_ne _ _ _ ((Order.le_succ j).trans_lt hij).ne', hM hij, map_zero, neg_zero]

end Matrix

namespace Mathlib.Tactic.Hessenberg

open Matrix

variable {R : Type*} [CommRing R]

/-! ## The last-column expansion of the determinant of an upper Hessenberg matrix -/

section Expansion

variable {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)

theorem lastColMinor_eq_zero (hM : M.IsUpperHessenberg) {i a b : Fin k} (ha : i ≤ a) (hab : b < a) :
    M.lastColMinor i a b = 0 := by
  rw [lastColMinor, submatrix_apply, Fin.succAbove_castSucc_of_le i a ha,
    isUpperHessenberg_iff.mp hM]
  simpa only [Fin.orderSucc_castSucc, Fin.succ_lt_succ_iff] using hab

/-- `Tᵢ` is upper triangular, so its determinant is the product of its diagonal. -/
theorem det_toSquareBlockProp_not_lt (hM : M.IsUpperHessenberg) (i : Fin k) :
    ((M.lastColMinor i).toSquareBlockProp (¬ · < i)).det = ∏ j ∈ Ici i, M j.succ j.castSucc := by
  rw [toSquareBlockProp_lastColMinor_not_lt, det_of_isUpperTriangular]
  · simp only [of_apply]
    symm
    apply prod_subtype
    simp
  · exact fun a b hab => isUpperHessenberg_iff.mp hM (by simpa [Fin.orderSucc_castSucc] using hab)

/-- `Hᵢ` is block triangular, so `det Hᵢ = det Mᵢ · det Tᵢ`. -/
theorem det_lastColMinor (hM : M.IsUpperHessenberg) (i : Fin k) :
    (M.lastColMinor i).det =
      (M.leadingBlock i.castSucc.isLt.le).det * ∏ j ∈ Ici i, M j.succ j.castSucc := by
  rw [twoBlockTriangular_det _ (· < i) fun a ha b hb =>
      lastColMinor_eq_zero M hM (not_lt.mp ha) (hb.trans_le (not_lt.mp ha)),
    ← det_submatrix_equiv_self (Fin.castLEquiv i.isLt.le), toSquareBlockProp_lastColMinor,
    det_toSquareBlockProp_not_lt M hM i]

/-- The determinant of an upper Hessenberg matrix, expanded along its last column. -/
theorem det_eq_sum_of_isUpperHessenberg (hM : M.IsUpperHessenberg) :
    M.det = M (Fin.last k) (Fin.last k) * (M.leadingBlock k.le_succ).det +
      ∑ i : Fin k, M i.castSucc (Fin.last k) *
        ((M.leadingBlock i.castSucc.isLt.le).det * ∏ j ∈ Ici i, -M j.succ j.castSucc) := by
  rw [det_succ_column M (Fin.last k), Fin.sum_univ_castSucc, Fin.succAbove_last, add_comm]
  congrm ?_ + ∑ i, ?_
  · rw [Even.neg_one_pow, one_mul]
    · rfl
    · apply Even.add_self
  · rw [det_lastColMinor M hM, prod_neg, Fin.card_Ici,
      neg_one_pow_congr (n := k - i) (by rw [Nat.even_add, Nat.even_sub i.isLt.le]; exact Iff.comm)]
    ring

end Expansion

variable {n : ℕ}

/-! ## The characteristic polynomial recurrence -/

/-- Computation of the characteristic polynomial of an upper Hessenberg matrix by Laplace expansion
of the determinant of its characteristic matrix. -/
theorem charpoly_isUpperHessenberg {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (hM : M.IsUpperHessenberg) :
    M.charpoly = (X - C (M (Fin.last k) (Fin.last k))) * (M.leadingBlock k.le_succ).charpoly -
      ∑ t : Fin k, C (M t.castSucc (Fin.last k) * ∏ j ∈ Ici t, M j.succ j.castSucc) *
        (M.leadingBlock t.castSucc.isLt.le).charpoly := by
  have hlast (t : Fin k) : M.charmatrix t.castSucc (Fin.last k) = -C (M t.castSucc (Fin.last k)) :=
    charmatrix_apply_ne _ _ _ (Fin.castSucc_ne_last t)
  have hsub (j : Fin k) : M.charmatrix j.succ j.castSucc = -C (M j.succ j.castSucc) :=
    charmatrix_apply_ne _ _ _ Fin.castSucc_lt_succ.ne'
  simp only [charpoly, charmatrix_leadingBlock, det_eq_sum_of_isUpperHessenberg _ hM.charmatrix,
    charmatrix_apply_eq, hlast, hsub, neg_neg, C_mul, map_prod, sub_eq_add_neg, ← sum_neg_distrib]
  congrm _ + ∑ t, ?_
  ring

/-- The recurrence formula computes the characteristic polynomial of an upper Hessenberg matrix
represented an array of entries stored in row-major order -/
theorem hessP_eq_charpoly {H : Array R} (hsize : H.size = n * n)
    (hH : (ofArray H hsize).IsUpperHessenberg) (k : ℕ) (hk : k ≤ n) :
    hessP n H k = ((ofArray H hsize).leadingBlock hk).charpoly := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [hessP_zero, charpoly_isEmpty]
    | succ k =>
      rw [hessP_succ, charpoly_isUpperHessenberg _ (hH.leadingBlock hk)]
      simp (disch := omega) only [ih, leadingBlock_leadingBlock, leadingBlock_apply,
        ofArray_eq_of_getD, of_apply, Fin.val_castLE, Fin.val_castSucc, Fin.val_last, Fin.val_succ,
        ← Fin.map_valEmbedding_Ici, prod_map, Fin.valEmbedding_apply]

/-- The characteristic polynomial of an upper Hessenberg matrix is computed by the
leading-principal-block recurrence on the row-major array of its entries. -/
public theorem charpoly_eq_hessCharPoly (H : Matrix (Fin n) (Fin n) R) (hH : H.IsUpperHessenberg) :
    H.charpoly = hessCharPoly n H.toArray := by
  rw [hessCharPoly_eq, hessP_eq_charpoly H.size_toArray (by rwa [ofArray_toArray]) n le_rfl,
    ofArray_toArray, leadingBlock_self]

end Mathlib.Tactic.Hessenberg
