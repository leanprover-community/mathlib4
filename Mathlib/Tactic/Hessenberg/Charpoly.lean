/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.LinearAlgebra.Matrix.Array
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs

/-!
# The characteristic polynomial recurrence for upper Hessenberg matrices

This file contains a recurrence formula for the characteristic polynomial of an upper Hessenberg
matrix, in a noncomputable and a computable form, and a proof that the recurrence computes
`Matrix.charpoly`.

The recurrence comes from equation 5.1 of [Rehman-Ipsen][rehmanipsen2011]. For an `n × n` upper
Hessenberg matrix `H` it successively computes the characteristic polynomials
`pᵢ(X) = det (X * I - Hᵢ)` of the leading principal submatrices `Hᵢ` of order `i`:

```
p_0 := 1

p_{k+1} = (X - C H[k][k]) p_k - ∑_{t<k} C (H[t][k] ∏_{j=t}^{k-1} H[j+1][j]) p_t
```

## Main definitions

- `hessP n H k`: the polynomial `pₖ` of the recurrence, in `R[X]`.
- `hessCharpoly n H`: the characteristic polynomial computed by the recurrence in `R[X]`.
- `coeffHessCharpoly n H`: the characteristic polynomial computed by the recurrence on polynomials
  represented as lists of coefficients.

We have both `hessCharpoly` and `coeffHessCharpoly` so that for a literal matrix `H` we can produce
the coefficients of the characteristic polynomial by computing `coeffHessCharpoly` using the kernel.
The theorem `ofCoeffList_coeffHessCharpoly` interprets the result as `hessCharpoly`, a polynomial in
`R[X]`.

## Main results

- `ofCoeffList_coeffHessCharpoly`: the recurrence on coefficient lists computes `hessCharpoly n H`.
- `charpoly_eq_hessCharpoly`: `hessCharpoly` computes the characteristic polynomial of an upper
  Hessenberg matrix.

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

The leading principal submatrices `Hᵢ` are also upper Hessenberg, so the same expansion applies to
`p₀, ..., p_{n-1}`, which gives the recurrence formula above.

In the formalization:

- `Matrix.leadingBlock` defines the leading principal submatrix.
- `IsUpperHessenberg.charmatrix` and `charmatrix_leadingBlock` show that `CH` is upper Hessenberg
  with `Mₖ` the characteristic matrix of `Hₖ`.
- `det_lastColMinor` is the formula for `det Hᵢ`.
- `det_eq_sum_of_isUpperHessenberg` is the expansion of `det CH` along its last column.
- `charpoly_isUpperHessenberg` specializes the determinant expansion to `CH`.
- `hessP_eq_charpoly` is the proof of the recurrence formula.

## References

* [Rizwana Rehman, Ilse C. F. Ipsen,
  *La Budde's method for computing characteristic polynomials*][rehmanipsen2011]
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] (n : ℕ) (H : Array R)

/-- The characteristic polynomial of the leading `k × k` block of the `n × n` Hessenberg
matrix represented by an array of entries in row-major ordering. -/
noncomputable def hessP : ℕ → R[X]
  | 0 => 1
  | k + 1 =>
    (X - C (H.getD (n * k + k) 0)) * hessP k -
      ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
        ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) * hessP (t : ℕ)

/-- The characteristic polynomial of an `n × n` Hessenberg matrix represented by an array of
entries in row-major ordering. -/
noncomputable abbrev hessCharpoly : R[X] := hessP n H n

variable {n H}

theorem hessP_zero : hessP n H 0 = 1 := by
  simp only [hessP]

theorem hessP_succ (k : ℕ) :
    hessP n H (k + 1) =
      (X - C (H.getD (n * k + k) 0)) * hessP n H k -
        ∑ t : Fin k, C (H.getD (n * (t : ℕ) + k) 0 *
          ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
          hessP n H (t : ℕ) := by
  simp only [hessP]

theorem hessCharpoly_eq : hessCharpoly n H = hessP n H n := rfl

/-! ## The recurrence on coefficient lists

This section defines the recurrence on a polynomial representation (lists of coefficients) that the
kernel can compute.
-/

variable (n H)

/-- Compute the coefficients of `∑_{t ≤ i} H[t][k] · r · (∏_{j=t}^{i-1} H[j+1][j]) · p_t` by
recursion on `i`, where `p_t` is the polynomial defined in the coefficient list `ps[t]`. `r`
accumulates the product of `H[i+1][i]` entries at each step. -/
@[expose]
def coeffHessSum (k : ℕ) :
    (i : ℕ) → (r : R) → (ps : Array (List R)) → List R
  | 0, r, ps => (ps.getD 0 []).map (H.getD (n * 0 + k) 0 * r * ·)
  | i + 1, r, ps =>
    List.zipWithAll (fun a b => a.getD 0 + b.getD 0)
      ((ps.getD (i + 1) []).map (H.getD (n * (i + 1) + k) 0 * r * ·))
      (coeffHessSum k i (r * H.getD (n * (i + 1) + i) 0) ps)

/-- Compute the coefficients of `pₖ` from the coefficient lists of `p₀, ..., p_{k-1}`. The
coefficients of each polynomial are stored as a `List R` in `ps`. -/
@[expose]
def coeffHessStep (k : ℕ) (ps : Array (List R)) : List R :=
  match k with
  | 0 => [1]
  | 1 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD 0 [])
      ((ps.getD 0 []).map (H.getD (n * 0 + 0) 0 * ·))
  | k' + 2 =>
    List.zipWithAll (fun a b => a.getD 0 - b.getD 0)
      (List.zipWithAll (fun a b => a.getD 0 - b.getD 0) (0 :: ps.getD (k' + 1) [])
        ((ps.getD (k' + 1) []).map (H.getD (n * (k' + 1) + (k' + 1)) 0 * ·)))
      (coeffHessSum n H (k' + 1) k' (H.getD (n * (k' + 1) + k') 0) ps)

/-- Compute the coefficients of `hessCharpoly n H`. -/
@[expose]
def coeffHessCharpoly : List R :=
  ((fun ps => ps.push (coeffHessStep n H ps.size ps))^[n] #[[1]]).getD n []

variable {n H}

theorem ofCoeffList_coeffHessSum (k : ℕ) :
    ∀ (i : ℕ) (r : R) (ps : Array (List R)),
      ofCoeffList (coeffHessSum n H k i r ps) =
        ∑ t : Fin (i + 1),
          C (H.getD (n * (t : ℕ) + k) 0 *
              (r * ∏ j ∈ Finset.Ico (t : ℕ) i, H.getD (n * (j + 1) + j) 0)) *
            ofCoeffList (ps.getD (t : ℕ) [])
  | 0, r, ps => by simp [coeffHessSum]
  | i + 1, r, ps => by
    rw [coeffHessSum, ofCoeffList_zipWithAll_add, ofCoeffList_coeffHessSum,
      Fin.sum_univ_succAbove _ (.last (i + 1))]
    congrm ?_ + ∑ t, ?_ <;> simp [Finset.prod_Ico_succ_top, Fin.is_le]
    ring

theorem ofCoeffList_coeffHessStep (k : ℕ) (ps : Array (List R)) :
    ofCoeffList (coeffHessStep n H (k + 1) ps) =
      (X - C (H.getD (n * k + k) 0)) * ofCoeffList (ps.getD k []) -
        ∑ t : Fin k,
          C (H.getD (n * (t : ℕ) + k) 0 * ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
            ofCoeffList (ps.getD (t : ℕ) []) := by
  cases k with
  | zero =>
    simp [coeffHessStep, sub_mul]
  | succ k =>
    rw [coeffHessStep, ofCoeffList_zipWithAll_sub, ofCoeffList_zipWithAll_sub,
      ofCoeffList_zero_cons, ofCoeffList_map_mul, ofCoeffList_coeffHessSum, sub_mul]
    congrm _ - ∑ t, ?_
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

@[simp]
theorem ofCoeffList_coeffHessCharpoly :
    ofCoeffList (coeffHessCharpoly n H) = hessCharpoly n H := by
  let f (ps : Array (List R)) := ps.push (coeffHessStep n H ps.size ps)
  have hsize k : (f^[k] #[[1]]).size = k + 1 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Array.size_push, ih]
  suffices ∀ k, ∀ m ≤ k, ofCoeffList ((f^[k] #[[1]]).getD m []) = hessP n H m from this n n le_rfl
  intro k
  induction k with
  | zero => simp [ofCoeffList_cons, hessP_zero]
  | succ k ih =>
    intro m hm
    rw [Function.iterate_succ_apply', Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize]
    split_ifs with hmk
    · rw [Option.getD_some, hmk, ofCoeffList_coeffHessStep, hessP_succ]
      aesop
    · rw [← Array.getD_eq_getD_getElem?, ih m (by lia)]

end Mathlib.Tactic.Hessenberg

end

/-! ## Correctness of the recurrence -/

open Polynomial Finset

namespace Matrix

variable {α : Type*} {k n : ℕ}

/-- The leading `k × k` block of an `n × n` matrix. -/
def leadingBlock (M : Matrix (Fin n) (Fin n) α) (h : k ≤ n) : Matrix (Fin k) (Fin k) α :=
  M.submatrix (Fin.castLE h) (Fin.castLE h)

@[simp]
theorem leadingBlock_apply (M : Matrix (Fin n) (Fin n) α) (h : k ≤ n) (i j : Fin k) :
    M.leadingBlock h i j = M (Fin.castLE h i) (Fin.castLE h j) := rfl

@[simp]
theorem leadingBlock_self (M : Matrix (Fin n) (Fin n) α) : M.leadingBlock le_rfl = M := rfl

/-- The minor `Hᵢ` formed from `M` by deleting the `i`th row and the last column. -/
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

theorem charmatrix_leadingBlock [CommRing α] (M : Matrix (Fin n) (Fin n) α)
    (h : k ≤ n) : (M.leadingBlock h).charmatrix = M.charmatrix.leadingBlock h := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem IsUpperHessenberg.leadingBlock [Zero α] {M : Matrix (Fin n) (Fin n) α}
    (hM : M.IsUpperHessenberg) (h : k ≤ n) : (M.leadingBlock h).IsUpperHessenberg := by
  rw [isUpperHessenberg_iff] at hM ⊢
  intro _ _ hij
  exact hM (by simpa [Fin.orderSucc_lt_iff] using hij)

theorem IsUpperHessenberg.charmatrix [CommRing α] {M : Matrix (Fin n) (Fin n) α}
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

/-! ## The recurrence computes the characteristic polynomial -/

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
represented by an array of entries stored in row-major order. -/
theorem hessP_eq_charpoly {H : Array R} (hsize : H.size = n * n)
    (hH : (ofArray H hsize).IsUpperHessenberg) (k : ℕ) (hk : k ≤ n) :
    hessP n H k = ((ofArray H hsize).leadingBlock hk).charpoly := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => rw [hessP_zero, charpoly_isEmpty]
    | succ k =>
      have ih' (t : Fin k) := ih t (by lia) (by lia)
      simp_rw [hessP_succ, charpoly_isUpperHessenberg _ (hH.leadingBlock hk),
        ih k (by lia) (by lia), ih', ofArray_eq_of_getD, ← Fin.map_valEmbedding_Ici, prod_map]
      aesop

/-- The characteristic polynomial of an upper Hessenberg matrix is computed by the
leading-principal-block recurrence on the row-major array of its entries. -/
public theorem charpoly_eq_hessCharpoly (H : Matrix (Fin n) (Fin n) R) (hH : H.IsUpperHessenberg) :
    H.charpoly = hessCharpoly n H.toArray := by
  rw [hessCharpoly_eq, hessP_eq_charpoly H.size_toArray (by rwa [ofArray_toArray]) n le_rfl,
    ofArray_toArray, leadingBlock_self]

end Mathlib.Tactic.Hessenberg
