/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import HexPoly

/-!
Equivalence between the executable `Hex.DensePoly`
representation and Mathlib's `Polynomial`.

This module provides the concrete conversion functions and ring equivalence
used by downstream proof-transfer libraries.
-/

public section

open scoped BigOperators

namespace HexPolyMathlib

universe u v

variable {R : Type u}

noncomputable section

/-- Reading a mapped `List.range` with default zero returns the mapped index inside
the range and zero outside it. This is the coefficient-array lookup fact used by
`coeff_ofPolynomial` when rebuilding dense polynomials from Mathlib coefficients. -/
theorem list_getD_map_range_zero [Zero R] (size n : Nat) (f : Nat → R) :
    (List.map f (List.range size)).getD n (Zero.zero : R) =
      if n < size then f n else (Zero.zero : R) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- Interpret a normalized dense coefficient array as a Mathlib polynomial. -/
@[expose]
def toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) : Polynomial R :=
  Finset.sum (Finset.range p.size) fun i => Polynomial.monomial i (p.coeff i)

/-- Rebuild a normalized dense polynomial from the coefficients of a Mathlib polynomial. -/
@[expose]
def ofPolynomial [Semiring R] [DecidableEq R] (p : Polynomial R) : Hex.DensePoly R :=
  Hex.DensePoly.ofList ((List.range (p.natDegree + 1)).map p.coeff)

/-- Rebuilding via `ofPolynomial` preserves coefficients: the `n`th coefficient
of `ofPolynomial p` agrees with the `n`th coefficient of `p`. -/
@[simp, grind =]
theorem coeff_ofPolynomial [Semiring R] [DecidableEq R] (p : Polynomial R) (n : Nat) :
    (ofPolynomial p).coeff n = p.coeff n := by
  unfold ofPolynomial
  rw [Hex.DensePoly.coeff_ofList, list_getD_map_range_zero]
  by_cases hn : n < p.natDegree + 1
  · simp [hn]
  · have hlt : p.natDegree < n := by omega
    simp [hn, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    rfl

/-- The `i`th diagonal contribution to the coefficient of degree `n` in the
product of two dense polynomials. It is zero past the diagonal and otherwise
denotes `p.coeff i * q.coeff (n - i)`, the term later summed in
`mulCoeffSum_eq_diagonal`. -/
private def denseDiagonalMulCoeffTerm [Zero R] [DecidableEq R] [Mul R]
    (p q : Hex.DensePoly R) (n i : Nat) : R :=
  if n < i then 0 else p.coeff i * q.coeff (n - i)

/-- The bounded version of `denseDiagonalMulCoeffTerm` seen by an inner
`List.range m` fold. It keeps only diagonal terms whose second index is within
the current bound, forming the correspondence from `mulCoeffStep` to the unbounded
diagonal term. -/
private def denseBoundedDiagonalMulCoeffTerm [Zero R] [DecidableEq R] [Mul R]
    (p q : Hex.DensePoly R) (n i m : Nat) : R :=
  if n < i then 0 else if n - i < m then p.coeff i * q.coeff (n - i) else 0

/-- Folding `mulCoeffStep` over a bounded range adds exactly the bounded
diagonal contribution for the fixed outer index `i`. This is the inner-fold
normal form used before replacing the bound by `q.size`. -/
private theorem fold_mulCoeffStep_eq_bounded_diagonal [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n i m : Nat) (acc : R) :
    (List.range m).foldl (Hex.DensePoly.mulCoeffStep p q n i) acc =
      acc + denseBoundedDiagonalMulCoeffTerm p q n i m := by
  induction m generalizing acc with
  | zero =>
      simp [denseBoundedDiagonalMulCoeffTerm]
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold Hex.DensePoly.mulCoeffStep denseBoundedDiagonalMulCoeffTerm
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          have hle : n ≤ m + i := by omega
          simp [hlt, hm, hne, hle]
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- Folding `mulCoeffStep` over all coefficients of `q` adds the full diagonal
term for the fixed outer index `i`. Coefficients outside `q.size` vanish, so this
removes the bounded inner-fold artifact. -/
private theorem fold_mulCoeffStep_eq_diagonal [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n i : Nat) (acc : R) :
    (List.range q.size).foldl (Hex.DensePoly.mulCoeffStep p q n i) acc =
      acc + denseDiagonalMulCoeffTerm p q n i := by
  rw [fold_mulCoeffStep_eq_bounded_diagonal]
  unfold denseBoundedDiagonalMulCoeffTerm denseDiagonalMulCoeffTerm
  by_cases hlt : n < i
  · simp [hlt]
  · by_cases hbound : n - i < q.size
    · simp [hlt, hbound]
    · have hcoeff : q.coeff (n - i) = 0 :=
        Hex.DensePoly.coeff_eq_zero_of_size_le q (Nat.le_of_not_gt hbound)
      simp [hlt, hbound, hcoeff]

/-- Replacing every inner multiplication fold by its diagonal contribution gives
the same outer fold over any list of outer indices. This lifts the fixed-index
inner-fold normal form to the nested fold used by `mulCoeffSum`. -/
private theorem fold_mulCoeff_outer_eq_diagonal [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n : Nat) (xs : List Nat) (acc : R) :
    xs.foldl (fun coeff i => (List.range q.size).foldl
        (Hex.DensePoly.mulCoeffStep p q n i) coeff) acc =
      xs.foldl (fun coeff i => coeff + denseDiagonalMulCoeffTerm p q n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [fold_mulCoeffStep_eq_diagonal]
      exact ih (acc + denseDiagonalMulCoeffTerm p q n i)

/-- The executable multiplication coefficient sum is the fold over diagonal
contributions indexed by the size of the left factor. This is the main normal
form used by `toPolynomial_mul` before converting the range fold to a Finset sum. -/
private theorem mulCoeffSum_eq_diagonal [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n : Nat) :
    Hex.DensePoly.mulCoeffSum p q n =
      (List.range p.size).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 := by
  unfold Hex.DensePoly.mulCoeffSum
  exact fold_mulCoeff_outer_eq_diagonal p q n (List.range p.size) 0

/-- A diagonal contribution is zero once its left index is outside the stored
coefficient range of `p`. This permits extending the diagonal fold beyond
`p.size` without changing its value. -/
private theorem denseDiagonalMulCoeffTerm_eq_zero_of_size_le [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n i : Nat) (hi : p.size ≤ i) :
    denseDiagonalMulCoeffTerm p q n i = 0 := by
  unfold denseDiagonalMulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : p.coeff i = 0 := Hex.DensePoly.coeff_eq_zero_of_size_le p hi
    simp [hn, hcoeff]

/-- Extending the diagonal fold by any number of indices past `p.size` does not
change the sum. The added terms vanish by
`denseDiagonalMulCoeffTerm_eq_zero_of_size_le`. -/
private theorem fold_diagonal_extend [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n d : Nat) :
    (List.range (p.size + d)).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 =
      (List.range p.size).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : denseDiagonalMulCoeffTerm p q n (p.size + d) = 0 :=
        denseDiagonalMulCoeffTerm_eq_zero_of_size_le p q n (p.size + d) (by omega)
      simp [hterm]

/-- The diagonal fold can be evaluated over any range whose size is at least
`p.size`. This packages `fold_diagonal_extend` for later comparison with the
degree-indexed range used by Mathlib's coefficient formula. -/
private theorem diagonalSum_eq_bound [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n m : Nat) (hm : p.size ≤ m) :
    (List.range p.size).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 =
      (List.range m).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 := by
  have hm' : p.size + (m - p.size) = m := by omega
  rw [← hm']
  exact (fold_diagonal_extend p q n (m - p.size)).symm

/-- A diagonal contribution is zero when the left index is larger than the target
degree `n`. This is the degree-side vanishing fact used to truncate diagonal
folds to `n + 1` terms. -/
private theorem denseDiagonalMulCoeffTerm_eq_zero_of_degree_lt [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n i : Nat) (hi : n < i) :
    denseDiagonalMulCoeffTerm p q n i = 0 := by
  simp [denseDiagonalMulCoeffTerm, hi]

/-- Extending the degree-indexed diagonal fold past `n + 1` leaves the sum
unchanged. The extra indices cannot lie on the degree-`n` multiplication
diagonal, so their contributions are zero. -/
private theorem fold_diagonal_truncate_degree [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : denseDiagonalMulCoeffTerm p q n (n + 1 + d) = 0 :=
        denseDiagonalMulCoeffTerm_eq_zero_of_degree_lt p q n (n + 1 + d) (by omega)
      simp [hterm]

/-- The diagonal fold over `p.size` agrees with the canonical degree bound
`n + 1`. This aligns `mulCoeffSum_eq_diagonal` with the range used by Mathlib's
antidiagonal coefficient formula in `toPolynomial_mul`. -/
private theorem diagonalSum_eq_degree_bound [Semiring R] [DecidableEq R]
    (p q : Hex.DensePoly R) (n : Nat) :
    (List.range p.size).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + denseDiagonalMulCoeffTerm p q n i) 0 := by
  by_cases hsize : p.size ≤ n + 1
  · exact diagonalSum_eq_bound p q n (n + 1) hsize
  · have hsize' : n + 1 + (p.size - (n + 1)) = p.size := by omega
    rw [← hsize']
    exact fold_diagonal_truncate_degree p q n (p.size - (n + 1))

/-- A left fold that repeatedly adds `f i` over `List.range m` is the same as
the corresponding `Finset.range` sum. This is the final fold-to-sum correspondence used
before comparing executable multiplication with Mathlib polynomial multiplication. -/
private theorem range_foldl_add_eq_finset_sum [AddCommMonoid R] (f : Nat → R) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

/-- Converting via `toPolynomial` preserves coefficients: the `n`th coefficient
of `toPolynomial p` agrees with the `n`th coefficient of the dense polynomial `p`. -/
@[simp, grind =]
theorem coeff_toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n := by
  unfold toPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < p.size
  · simp [Polynomial.coeff_monomial, hn]
  · have hcoeff := Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt hn)
    rw [Finset.sum_eq_zero]
    · rw [hcoeff]
      rfl
    · intro i hi
      have hi_lt : i < p.size := Finset.mem_range.mp hi
      have hne : i ≠ n := by omega
      simp [Polynomial.coeff_monomial, hne]

/-- Coefficient-sum evaluation correspondence: evaluating `toPolynomial p` through a ring
hom `f` at `x` is the degree-indexed sum `∑ f (p.coeff i) * x ^ i`. For a literal
`ofCoeffs` array this unfolds via `Finset.sum_range_succ` into an explicit
polynomial in `x`, which `ring`/`norm_num` can then discharge. -/
theorem eval₂_toPolynomial {S : Type*} [Semiring R] [DecidableEq R] [Semiring S]
    (f : R →+* S) (p : Hex.DensePoly R) (x : S) :
    (toPolynomial p).eval₂ f x = ∑ i ∈ Finset.range p.size, f (p.coeff i) * x ^ i := by
  unfold toPolynomial
  rw [Polynomial.eval₂_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Polynomial.eval₂_monomial f x

/-- Horner list evaluation as a range sum, the shape Mathlib's
`Polynomial.eval` lemmas produce. -/
private theorem evalCoeffList_eq_sum [Semiring R] (l : List R) (x : R) :
    Hex.DensePoly.evalCoeffList l x
      = ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i := by
  induction l with
  | nil =>
      rw [show Hex.DensePoly.evalCoeffList ([] : List R) x = (0 : R)
        from rfl]
      simp
  | cons c cs ih =>
      rw [show Hex.DensePoly.evalCoeffList (c :: cs) x
          = Hex.DensePoly.evalCoeffList cs x * x + c from rfl, ih,
        List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
      simp [pow_succ, mul_assoc]

/-- Mathlib evaluation of a converted dense polynomial is the
executable dense Horner evaluation. -/
@[simp]
theorem eval_toPolynomial [Semiring R] [DecidableEq R]
    (p : Hex.DensePoly R) (x : R) :
    (toPolynomial p).eval x = p.eval x := by
  change (∑ i ∈ Finset.range p.size,
    Polynomial.monomial i (p.coeff i)).eval x
      = Hex.DensePoly.evalCoeffList p.toList x
  rw [Polynomial.eval_finsetSum, evalCoeffList_eq_sum,
    Hex.DensePoly.length_toList]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_monomial]
  exact congrArg (· * x ^ i) (Hex.DensePoly.toList_getD_eq_coeff p i).symm

/-- `ofPolynomial` sends Mathlib's zero polynomial to the executable zero. -/
@[simp, grind =]
theorem ofPolynomial_zero [Semiring R] [DecidableEq R] :
    ofPolynomial (0 : Polynomial R) = 0 := by
  apply Hex.DensePoly.ext_coeff
  intro n
  simp [coeff_ofPolynomial, Hex.DensePoly.coeff_zero]

/-- `ofPolynomial` sends Mathlib's polynomial `1` to the executable constant `1`. -/
@[simp, grind =]
theorem ofPolynomial_one [Semiring R] [DecidableEq R] :
    ofPolynomial (1 : Polynomial R) = 1 := by
  change ofPolynomial (1 : Polynomial R) = Hex.DensePoly.C 1
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [coeff_ofPolynomial, Hex.DensePoly.coeff_C, Polynomial.coeff_one]
  rfl

/-- `ofPolynomial` sends Mathlib's polynomial constant to the executable constant. -/
@[simp, grind =]
theorem ofPolynomial_C [Semiring R] [DecidableEq R] (c : R) :
    ofPolynomial (Polynomial.C c) = Hex.DensePoly.C c := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [coeff_ofPolynomial, Hex.DensePoly.coeff_C, Polynomial.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    rfl

/-- `ofPolynomial` commutes with polynomial negation. -/
@[simp, grind =]
theorem ofPolynomial_neg [Ring R] [DecidableEq R] (p : Polynomial R) :
    ofPolynomial (-p) = -ofPolynomial p := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_neg _ _ (by change (0 : R) - 0 = 0; simp)]
  simp [coeff_ofPolynomial, Polynomial.coeff_neg]

/-- `ofPolynomial` commutes with polynomial subtraction. -/
@[simp, grind =]
theorem ofPolynomial_sub [Ring R] [DecidableEq R] (p q : Polynomial R) :
    ofPolynomial (p - q) = ofPolynomial p - ofPolynomial q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_sub _ _ _ (by change (0 : R) - 0 = 0; simp)]
  simp [coeff_ofPolynomial, Polynomial.coeff_sub]

/-- `ofPolynomial` commutes with polynomial addition. -/
@[simp, grind =]
theorem ofPolynomial_add [Semiring R] [DecidableEq R] (p q : Polynomial R) :
    ofPolynomial (p + q) = ofPolynomial p + ofPolynomial q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_add _ _ _ (by change (0 : R) + 0 = 0; simp)]
  simp [coeff_ofPolynomial, Polynomial.coeff_add]

/-- `ofPolynomial` sends Mathlib's monomial to the executable monomial. -/
@[simp, grind =]
theorem ofPolynomial_monomial [Semiring R] [DecidableEq R] (n : Nat) (c : R) :
    ofPolynomial (Polynomial.monomial n c) = Hex.DensePoly.monomial n c := by
  apply Hex.DensePoly.ext_coeff
  intro i
  rw [coeff_ofPolynomial, Hex.DensePoly.coeff_monomial,
      Polynomial.coeff_monomial]
  by_cases hi : i = n
  · simp [hi]
  · simp [hi, Ne.symm hi]
    rfl

/-- `toPolynomial` sends the executable zero to Mathlib's zero polynomial. -/
@[simp, grind =]
theorem toPolynomial_zero [Semiring R] [DecidableEq R] :
    toPolynomial (0 : Hex.DensePoly R) = 0 := by
  ext n
  simp [coeff_toPolynomial, Hex.DensePoly.coeff_zero]

/-- `toPolynomial` sends the executable constant to Mathlib's polynomial constant. -/
@[simp, grind =]
theorem toPolynomial_C [Semiring R] [DecidableEq R] (c : R) :
    toPolynomial (Hex.DensePoly.C c) = Polynomial.C c := by
  ext n
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_C, Polynomial.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    rfl

/-- `toPolynomial` sends the executable constant `1` to Mathlib's polynomial `1`. -/
@[simp, grind =]
theorem toPolynomial_one [Semiring R] [DecidableEq R] :
    toPolynomial (1 : Hex.DensePoly R) = 1 := by
  change toPolynomial (Hex.DensePoly.C 1) = 1
  rw [toPolynomial_C, Polynomial.C_1]

/-- `toPolynomial` reads a raw coefficient array off as the obvious sum,
ascending. This is what makes a concrete `#p[...]` literal readable on the
Mathlib side: with `Finset.sum_range_succ` to expand the range,
`toPolynomial #p[1, 1, 1]` becomes `C 1 * X ^ 0 + C 1 * X ^ 1 + C 1 * X ^ 2`.

Stated with `C _ * X ^ i` rather than `monomial i _` because that is the form a
reader writes a polynomial in, so a use site needs no `C_mul_X_pow_eq_monomial`
rewrite of its own. -/
@[simp, grind =]
theorem toPolynomial_ofCoeffs [Semiring R] [DecidableEq R] (cs : Array R) :
    toPolynomial (Hex.DensePoly.ofCoeffs cs) =
      ∑ i ∈ Finset.range cs.size,
        Polynomial.C (cs.getD i (Zero.zero : R)) * Polynomial.X ^ i := by
  ext n
  simp only [Polynomial.C_mul_X_pow_eq_monomial]
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_ofCoeffs, Polynomial.finsetSum_coeff]
  by_cases hn : n < cs.size
  · simp [Polynomial.coeff_monomial, hn]
  · rw [Finset.sum_eq_zero]
    · simp [Array.getD, hn]
      rfl
    · intro i hi
      have hne : i ≠ n := by
        have := Finset.mem_range.mp hi
        omega
      simp [Polynomial.coeff_monomial, hne]

/-- `toPolynomial` sends executable coefficient scaling to multiplication by
the corresponding constant polynomial. -/
@[simp, grind =]
theorem toPolynomial_scale [Semiring R] [DecidableEq R]
    (c : R) (p : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.scale c p) =
      Polynomial.C c * toPolynomial p := by
  ext n
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_scale_semiring,
    Polynomial.coeff_C_mul, coeff_toPolynomial]

/-- `toPolynomial` sends the executable monomial to Mathlib's monomial. -/
@[simp, grind =]
theorem toPolynomial_monomial [Semiring R] [DecidableEq R]
    (n : Nat) (c : R) :
    toPolynomial (Hex.DensePoly.monomial n c) = Polynomial.monomial n c := by
  ext i
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_monomial, Polynomial.coeff_monomial]
  by_cases h : i = n
  · simp [h]
  · have h' : n ≠ i := fun heq => h heq.symm
    simp [h, h']
    rfl

/-- `HexPolyMathlib.toPolynomial` commutes with polynomial addition. -/
@[simp, grind =]
theorem toPolynomial_add [Semiring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q := by
  ext n
  rw [coeff_toPolynomial, Polynomial.coeff_add, coeff_toPolynomial, coeff_toPolynomial]
  exact Hex.DensePoly.coeff_add p q n (by
    change (0 : R) + (0 : R) = 0
    simp)

/-- `toPolynomial` commutes with executable polynomial negation. -/
@[simp, grind =]
theorem toPolynomial_neg [Ring R] [DecidableEq R] (p : Hex.DensePoly R) :
    toPolynomial (-p) = -toPolynomial p := by
  ext n
  rw [coeff_toPolynomial, Polynomial.coeff_neg, coeff_toPolynomial,
      Hex.DensePoly.coeff_neg p n (by change (0 : R) - 0 = 0; simp), zero_sub]

/-- `toPolynomial` commutes with executable polynomial subtraction. -/
@[simp, grind =]
theorem toPolynomial_sub [Ring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q := by
  ext n
  rw [coeff_toPolynomial, Polynomial.coeff_sub, coeff_toPolynomial, coeff_toPolynomial]
  exact Hex.DensePoly.coeff_sub p q n (by
    change (0 : R) - (0 : R) = 0
    simp)

/-- `HexPolyMathlib.toPolynomial` commutes with polynomial
multiplication. -/
@[simp, grind =]
theorem toPolynomial_mul [Semiring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q := by
  ext n
  rw [coeff_toPolynomial, Polynomial.coeff_mul]
  simp_rw [coeff_toPolynomial]
  rw [Hex.DensePoly.coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound,
    range_foldl_add_eq_finset_sum]
  rw [show
      (∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2) =
        ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i) from
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => p.coeff i * q.coeff j) n]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : ¬ n < i := by
    have hi_lt : i < n + 1 := Finset.mem_range.mp hi
    omega
  simp [denseDiagonalMulCoeffTerm, hle]

/-- `HexPolyMathlib.toPolynomial` intertwines the executable derivative
with Mathlib's polynomial derivative. -/
@[simp, grind =]
theorem toPolynomial_derivative [CommSemiring R] [DecidableEq R] (p : Hex.DensePoly R) :
    toPolynomial p.derivative = Polynomial.derivative (toPolynomial p) := by
  ext n
  rw [coeff_toPolynomial, Hex.DensePoly.coeff_derivative p n (by
    change ((n + 1 : Nat) : R) * (0 : R) = 0
    rw [mul_zero]),
    Polynomial.coeff_derivative, coeff_toPolynomial]
  rw [Nat.cast_add, Nat.cast_one, mul_comm]

/-- Converting a Mathlib polynomial into the executable representation and back
recovers the original: `HexPolyMathlib.toPolynomial` is a left inverse of
`HexPolyMathlib.ofPolynomial`. -/
@[simp, grind =]
theorem toPolynomial_ofPolynomial [Semiring R] [DecidableEq R] (p : Polynomial R) :
    toPolynomial (ofPolynomial p) = p := by
  ext n
  simp [coeff_toPolynomial, coeff_ofPolynomial]

/-- Converting an executable polynomial into a Mathlib polynomial and back
recovers the original: `HexPolyMathlib.ofPolynomial` is a left inverse of
`HexPolyMathlib.toPolynomial`. -/
@[simp, grind =]
theorem ofPolynomial_toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) :
    ofPolynomial (toPolynomial p) = p := by
  apply Hex.DensePoly.ext_coeff
  intro n
  simp [coeff_ofPolynomial, coeff_toPolynomial]

/-- The executable dense-polynomial representation is ring-equivalent to Mathlib polynomials. -/
@[expose]
def equiv [Semiring R] [DecidableEq R] : Hex.DensePoly R ≃+* Polynomial R where
  toFun := toPolynomial
  invFun := ofPolynomial
  left_inv := ofPolynomial_toPolynomial
  right_inv := toPolynomial_ofPolynomial
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

/-- The ring isomorphism `equiv` is computed by `toPolynomial` in the forward
direction. -/
@[simp, grind =]
theorem equiv_apply [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) :
    equiv p = toPolynomial p := by
  rfl

/-- The inverse of the ring isomorphism `equiv` is computed by `ofPolynomial`. -/
@[simp, grind =]
theorem equiv_symm_apply [Semiring R] [DecidableEq R] (p : Polynomial R) :
    equiv.symm p = ofPolynomial p := by
  rfl

/-- Apply a coefficient-ring equivalence to a dense polynomial. -/
def mapEquiv {S : Type v} [Semiring R] [DecidableEq R]
    [Semiring S] [DecidableEq S] (e : R ≃+* S) :
    Hex.DensePoly R ≃+* Hex.DensePoly S :=
  equiv.trans <| (Polynomial.mapEquiv e).trans equiv.symm

@[simp] theorem mapEquiv_apply {S : Type v}
    [Semiring R] [DecidableEq R] [Semiring S] [DecidableEq S]
    (e : R ≃+* S) (p : Hex.DensePoly R) :
    mapEquiv e p =
      ofPolynomial (Polynomial.map e.toRingHom (toPolynomial p)) := by
  rfl

@[simp] theorem mapEquiv_symm_apply {S : Type v}
    [Semiring R] [DecidableEq R] [Semiring S] [DecidableEq S]
    (e : R ≃+* S) (p : Hex.DensePoly S) :
    (mapEquiv e).symm p =
      ofPolynomial (Polynomial.map e.symm.toRingHom (toPolynomial p)) := by
  rfl

/-- `ofPolynomial` commutes with polynomial multiplication. -/
@[simp, grind =]
theorem ofPolynomial_mul [Semiring R] [DecidableEq R] (p q : Polynomial R) :
    ofPolynomial (p * q) = ofPolynomial p * ofPolynomial q :=
  map_mul (equiv (R := R)).symm p q

/-- `HexPolyMathlib.toPolynomial` transports the executable degree to Mathlib's `natDegree`,
with the zero polynomial mapping to `0`. -/
@[simp, grind =]
theorem natDegree_toPolynomial [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) :
    (toPolynomial p).natDegree = p.degree?.getD 0 := by
  by_cases hsize : p.size = 0
  · have hp_zero : p = 0 := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)
    rw [hp_zero, toPolynomial_zero, Polynomial.natDegree_zero]
    simp [Hex.DensePoly.degree?]
  · have hpos : 0 < p.size := Nat.pos_of_ne_zero hsize
    have hdegree_some : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, hsize]
    rw [hdegree_some, Option.getD_some]
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      rw [coeff_toPolynomial]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [coeff_toPolynomial]
      exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size p hpos

/-- `toPolynomial` transports the executable leading coefficient to Mathlib's
`leadingCoeff`. -/
@[simp, grind =]
theorem leadingCoeff_toPolynomial [Semiring R] [DecidableEq R]
    (p : Hex.DensePoly R) :
    (toPolynomial p).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_toPolynomial, coeff_toPolynomial]
  by_cases hsize : p.size = 0
  · have hp_zero : p = 0 := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_zero]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le p (by omega)
    rw [hp_zero]
    simp [Hex.DensePoly.coeff_zero]
  · have hpos : 0 < p.size := Nat.pos_of_ne_zero hsize
    have hdegree_some : p.degree? = some (p.size - 1) := by
      simp [Hex.DensePoly.degree?, hsize]
    rw [hdegree_some, Option.getD_some]
    change p.coeff (p.size - 1) = p.leadingCoeff
    simp [Hex.DensePoly.leadingCoeff, Hex.DensePoly.coeff, Hex.DensePoly.size]

/-- `toPolynomial` preserves divisibility: a divisibility in the executable
representation transfers to the corresponding Mathlib polynomials. -/
theorem toPolynomial_dvd [Semiring R] [DecidableEq R] {p q : Hex.DensePoly R}
    (hdvd : p ∣ q) :
    toPolynomial p ∣ toPolynomial q := by
  rcases hdvd with ⟨r, hr⟩
  refine ⟨toPolynomial r, ?_⟩
  rw [← toPolynomial_mul, hr]

/-- `ofPolynomial` preserves divisibility: a divisibility of Mathlib polynomials
transfers to the corresponding executable representations. -/
theorem ofPolynomial_dvd [Semiring R] [DecidableEq R] {p q : Polynomial R}
    (hdvd : p ∣ q) :
    ofPolynomial p ∣ ofPolynomial q := by
  rcases hdvd with ⟨r, hr⟩
  refine ⟨ofPolynomial r, ?_⟩
  rw [← ofPolynomial_mul, hr]

/-- `HexPolyMathlib.toPolynomial` both preserves and reflects divisibility: executable
polynomials divide one another exactly when their Mathlib images do. -/
theorem toPolynomial_dvd_iff [Semiring R] [DecidableEq R]
    {p q : Hex.DensePoly R} :
    toPolynomial p ∣ toPolynomial q ↔ p ∣ q := by
  constructor
  · intro hdvd
    simpa using ofPolynomial_dvd (R := R) hdvd
  · exact toPolynomial_dvd

/-! # Composition -/

/-- The Horner polynomial built from a coefficient list, lowest degree first:
`hornerList (c :: cs) = C c + X * hornerList cs`. -/
private def hornerList [Semiring R] (l : List R) : Polynomial R :=
  l.foldr (fun c acc => Polynomial.C c + Polynomial.X * acc) 0

private theorem coeff_hornerList [Semiring R] : ∀ (l : List R) (n : ℕ),
    (hornerList l).coeff n = l.getD n 0
  | [], n => by simp [hornerList]
  | c :: cs, n => by
      change (Polynomial.C c + Polynomial.X * hornerList cs).coeff n = _
      cases n with
      | zero => simp
      | succ m =>
          rw [Polynomial.coeff_add, Polynomial.coeff_C, ite_eq_right (Nat.succ_ne_zero m),
            Polynomial.coeff_X_mul, coeff_hornerList cs m, zero_add, List.getD_cons_succ]

/-- Composition pushes through the Horner fold: substituting `M` for `X` turns
`hornerList l` into the same Horner fold with `M` in place of `X`. -/
private theorem hornerList_comp [CommSemiring R] (M : Polynomial R) : ∀ l : List R,
    (hornerList l).comp M = l.foldr (fun c acc => Polynomial.C c + M * acc) 0
  | [] => by simp [hornerList]
  | c :: cs => by
      change (Polynomial.C c + Polynomial.X * hornerList cs).comp M = _
      rw [Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp,
        hornerList_comp M cs]
      rfl

private theorem toList_getD [Semiring R] [DecidableEq R] (p : Hex.DensePoly R) (n : ℕ) :
    p.toList.getD n 0 = p.coeff n := by
  rw [Hex.DensePoly.toList, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have h := Hex.DensePoly.toArray_getD p n
  rw [Array.getD_eq_getD_getElem?] at h
  exact h

/-- Every executable dense polynomial is its own Horner list over the stored
coefficients. -/
private theorem toPolynomial_eq_hornerList [Semiring R] [DecidableEq R]
    (p : Hex.DensePoly R) :
    toPolynomial p = hornerList p.toList := by
  ext n
  rw [coeff_toPolynomial, coeff_hornerList, toList_getD]

/-- `toPolynomial` intertwines the executable Horner composition with Mathlib's
polynomial composition. -/
@[simp, grind =]
theorem toPolynomial_compose [CommSemiring R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.compose p q)
      = (toPolynomial p).comp (toPolynomial q) := by
  have hcl : ∀ l : List R, toPolynomial (Hex.DensePoly.composeCoeffList l q)
      = l.foldr (fun c acc => Polynomial.C c + toPolynomial q * acc) 0 := by
    intro l
    induction l with
    | nil => simp [Hex.DensePoly.composeCoeffList]
    | cons c cs ih =>
        change toPolynomial (Hex.DensePoly.composeCoeffList cs q * q + Hex.DensePoly.C c) = _
        rw [toPolynomial_add, toPolynomial_mul, toPolynomial_C, ih, List.foldr_cons,
          mul_comm, add_comm]
  change toPolynomial (Hex.DensePoly.composeCoeffList p.toList q) = _
  rw [hcl, toPolynomial_eq_hornerList p, hornerList_comp]

end

end HexPolyMathlib
