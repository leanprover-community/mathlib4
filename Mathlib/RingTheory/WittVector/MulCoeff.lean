/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import Mathlib.RingTheory.WittVector.Truncated
import Mathlib.Data.MvPolynomial.Supported

#align_import ring_theory.witt_vector.mul_coeff from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Leading terms of Witt vector multiplication

The goal of this file is to study the leading terms of the formula for the `n+1`st coefficient
of a product of Witt vectors `x` and `y` over a ring of characteristic `p`.
We aim to isolate the `n+1`st coefficients of `x` and `y`, and express the rest of the product
in terms of a function of the lower coefficients.

For most of this file we work with terms of type `MvPolynomial (Fin 2 × ℕ) ℤ`.
We will eventually evaluate them in `k`, but first we must take care of a calculation
that needs to happen in characteristic 0.

## Main declarations

* `WittVector.nth_mul_coeff`: expresses the coefficient of a product of Witt vectors
  in terms of the previous coefficients of the multiplicands.

-/


noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

variable {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

-- Porting note: new notation
local notation "𝕄" => MvPolynomial (Fin 2 × ℕ) ℤ

open Finset MvPolynomial

open scoped BigOperators

/--
```
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val) *
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)
```
-/
def wittPolyProd (n : ℕ) : 𝕄 :=
  rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ n) *
    rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ n)
#align witt_vector.witt_poly_prod WittVector.wittPolyProd

theorem wittPolyProd_vars (n : ℕ) : (wittPolyProd p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [wittPolyProd]
  -- ⊢ vars (↑(rename (Prod.mk 0)) (wittPolynomial p ℤ n) * ↑(rename (Prod.mk 1)) ( …
  apply Subset.trans (vars_mul _ _)
  -- ⊢ vars (↑(rename (Prod.mk 0)) (wittPolynomial p ℤ n)) ∪ vars (↑(rename (Prod.m …
  refine' union_subset _ _ <;>
  -- ⊢ vars (↑(rename (Prod.mk 0)) (wittPolynomial p ℤ n)) ⊆ univ ×ˢ range (n + 1)
  · refine' Subset.trans (vars_rename _ _) _
    -- ⊢ image (Prod.mk 0) (vars (wittPolynomial p ℤ n)) ⊆ univ ×ˢ range (n + 1)
    -- ⊢ image (Prod.mk 1) (vars (wittPolynomial p ℤ n)) ⊆ univ ×ˢ range (n + 1)
    -- 🎉 no goals
    simp [wittPolynomial_vars, image_subset_iff]
    -- 🎉 no goals
#align witt_vector.witt_poly_prod_vars WittVector.wittPolyProd_vars

/-- The "remainder term" of `WittVector.wittPolyProd`. See `mul_polyOfInterest_aux2`. -/
def wittPolyProdRemainder (n : ℕ) : 𝕄 :=
  ∑ i in range n, (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i)
#align witt_vector.witt_poly_prod_remainder WittVector.wittPolyProdRemainder

theorem wittPolyProdRemainder_vars (n : ℕ) :
    (wittPolyProdRemainder p n).vars ⊆ univ ×ˢ range n := by
  rw [wittPolyProdRemainder]
  -- ⊢ vars (∑ i in range n, ↑p ^ i * wittMul p i ^ p ^ (n - i)) ⊆ univ ×ˢ range n
  refine' Subset.trans (vars_sum_subset _ _) _
  -- ⊢ (Finset.biUnion (range n) fun i => vars (↑p ^ i * wittMul p i ^ p ^ (n - i)) …
  rw [biUnion_subset]
  -- ⊢ ∀ (x : ℕ), x ∈ range n → vars (↑p ^ x * wittMul p x ^ p ^ (n - x)) ⊆ univ ×ˢ …
  intro x hx
  -- ⊢ vars (↑p ^ x * wittMul p x ^ p ^ (n - x)) ⊆ univ ×ˢ range n
  apply Subset.trans (vars_mul _ _)
  -- ⊢ vars (↑p ^ x) ∪ vars (wittMul p x ^ p ^ (n - x)) ⊆ univ ×ˢ range n
  refine' union_subset _ _
  -- ⊢ vars (↑p ^ x) ⊆ univ ×ˢ range n
  · apply Subset.trans (vars_pow _ _)
    -- ⊢ vars ↑p ⊆ univ ×ˢ range n
    have : (p : 𝕄) = C (p : ℤ) := by simp only [Int.cast_ofNat, eq_intCast]
    -- ⊢ vars ↑p ⊆ univ ×ˢ range n
    rw [this, vars_C]
    -- ⊢ ∅ ⊆ univ ×ˢ range n
    apply empty_subset
    -- 🎉 no goals
  · apply Subset.trans (vars_pow _ _)
    -- ⊢ vars (wittMul p x) ⊆ univ ×ˢ range n
    apply Subset.trans (wittMul_vars _ _)
    -- ⊢ univ ×ˢ range (x + 1) ⊆ univ ×ˢ range n
    apply product_subset_product (Subset.refl _)
    -- ⊢ range (x + 1) ⊆ range n
    simp only [mem_range, range_subset] at hx ⊢
    -- ⊢ x + 1 ≤ n
    exact hx
    -- 🎉 no goals
#align witt_vector.witt_poly_prod_remainder_vars WittVector.wittPolyProdRemainder_vars

/-- `remainder p n` represents the remainder term from `mul_polyOfInterest_aux3`.
`wittPolyProd p (n+1)` will have variables up to `n+1`,
but `remainder` will only have variables up to `n`.
-/
def remainder (n : ℕ) : 𝕄 :=
  (∑ x : ℕ in range (n + 1),
    (rename (Prod.mk 0)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))) *
   ∑ x : ℕ in range (n + 1),
    (rename (Prod.mk 1)) ((monomial (Finsupp.single x (p ^ (n + 1 - x)))) ((p : ℤ) ^ x))
#align witt_vector.remainder WittVector.remainder

theorem remainder_vars (n : ℕ) : (remainder p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [remainder]
  -- ⊢ vars ((∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.sing …
  apply Subset.trans (vars_mul _ _)
  -- ⊢ vars (∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.singl …
  refine' union_subset _ _ <;>
  -- ⊢ vars (∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.singl …
  · refine' Subset.trans (vars_sum_subset _ _) _
    -- ⊢ (Finset.biUnion (range (n + 1)) fun i => vars (↑(rename (Prod.mk 0)) (↑(mono …
    -- ⊢ (Finset.biUnion (range (n + 1)) fun i => vars (↑(rename (Prod.mk 1)) (↑(mono …
    -- ⊢ ∀ (x : ℕ), x ∈ range (n + 1) → vars (↑(rename (Prod.mk 0)) (↑(monomial (Fins …
    rw [biUnion_subset]
    -- ⊢ vars (↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.single x (p ^ (n + 1 - x))) …
    -- ⊢ ∀ (x : ℕ), x ∈ range (n + 1) → vars (↑(rename (Prod.mk 1)) (↑(monomial (Fins …
    -- ⊢ (Finsupp.single (0, x) (p ^ (n + 1 - x))).support ⊆ univ ×ˢ range (n + 1)
    intro x hx
      -- ⊢ {(0, x)} ⊆ univ ×ˢ range (n + 1)
    -- ⊢ vars (↑(rename (Prod.mk 1)) (↑(monomial (Finsupp.single x (p ^ (n + 1 - x))) …
      -- 🎉 no goals
    rw [rename_monomial, vars_monomial, Finsupp.mapDomain_single]
      -- ⊢ ↑p ≠ 0
    -- ⊢ (Finsupp.single (1, x) (p ^ (n + 1 - x))).support ⊆ univ ×ˢ range (n + 1)
      -- 🎉 no goals
    · apply Subset.trans Finsupp.support_single_subset
      -- ⊢ {(1, x)} ⊆ univ ×ˢ range (n + 1)
      simpa using mem_range.mp hx
      -- 🎉 no goals
    · apply pow_ne_zero
      -- ⊢ ↑p ≠ 0
      exact_mod_cast hp.out.ne_zero
      -- 🎉 no goals
#align witt_vector.remainder_vars WittVector.remainder_vars

/-- This is the polynomial whose degree we want to get a handle on. -/
def polyOfInterest (n : ℕ) : 𝕄 :=
  wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
    X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
    X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1))
#align witt_vector.poly_of_interest WittVector.polyOfInterest

theorem mul_polyOfInterest_aux1 (n : ℕ) :
    ∑ i in range (n + 1), (p : 𝕄) ^ i * wittMul p i ^ p ^ (n - i) = wittPolyProd p n := by
  simp only [wittPolyProd]
  -- ⊢ ∑ i in range (n + 1), ↑p ^ i * wittMul p i ^ p ^ (n - i) = ↑(rename (Prod.mk …
  convert wittStructureInt_prop p (X (0 : Fin 2) * X 1) n using 1
  -- ⊢ ∑ i in range (n + 1), ↑p ^ i * wittMul p i ^ p ^ (n - i) = ↑(bind₁ (wittStru …
  · simp only [wittPolynomial, wittMul]
    -- ⊢ ∑ x in range (n + 1), ↑p ^ x * wittStructureInt p (X 0 * X 1) x ^ p ^ (n - x …
    rw [AlgHom.map_sum]
    -- ⊢ ∑ x in range (n + 1), ↑p ^ x * wittStructureInt p (X 0 * X 1) x ^ p ^ (n - x …
    congr 1 with i
    -- ⊢ MvPolynomial.coeff m✝ (↑p ^ i * wittStructureInt p (X 0 * X 1) i ^ p ^ (n -  …
    congr 1
    -- ⊢ ↑p ^ i * wittStructureInt p (X 0 * X 1) i ^ p ^ (n - i) = ↑(bind₁ (wittStruc …
    have hsupp : (Finsupp.single i (p ^ (n - i))).support = {i} := by
      rw [Finsupp.support_eq_singleton]
      simp only [and_true_iff, Finsupp.single_eq_same, eq_self_iff_true, Ne.def]
      exact pow_ne_zero _ hp.out.ne_zero
    simp only [bind₁_monomial, hsupp, Int.cast_ofNat, prod_singleton, eq_intCast,
      Finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, true_or_iff, eq_self_iff_true,
      Int.cast_pow]
  · simp only [map_mul, bind₁_X_right]
    -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_aux1 WittVector.mul_polyOfInterest_aux1

theorem mul_polyOfInterest_aux2 (n : ℕ) :
    (p : 𝕄) ^ n * wittMul p n + wittPolyProdRemainder p n = wittPolyProd p n := by
  convert mul_polyOfInterest_aux1 p n
  -- ⊢ ↑p ^ n * wittMul p n + wittPolyProdRemainder p n = ∑ i in range (n + 1), ↑p  …
  rw [sum_range_succ, add_comm, Nat.sub_self, pow_zero, pow_one]
  -- ⊢ wittPolyProdRemainder p n + ↑p ^ n * wittMul p n = ∑ x in range n, ↑p ^ x *  …
  rfl
  -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_aux2 WittVector.mul_polyOfInterest_aux2

theorem mul_polyOfInterest_aux3 (n : ℕ) : wittPolyProd p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    remainder p n := by
  -- a useful auxiliary fact
  have mvpz : (p : 𝕄) ^ (n + 1) = MvPolynomial.C ((p : ℤ) ^ (n + 1)) := by simp only; norm_cast
  -- ⊢ wittPolyProd p (n + 1) = -(↑p ^ (n + 1) * X (0, n + 1)) * (↑p ^ (n + 1) * X  …
  -- Porting note: the original proof applies `sum_range_succ` through a non-`conv` rewrite,
  -- but this does not work in Lean 4; the whole proof also times out very badly. The proof has been
  -- nearly totally rewritten here and now finishes quite fast.
  rw [wittPolyProd, wittPolynomial, AlgHom.map_sum, AlgHom.map_sum]
  -- ⊢ (∑ x in range (n + 1 + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.single …
  conv_lhs =>
    arg 1
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_lhs =>
    arg 2
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  conv_rhs =>
    enter [1, 2, 2]
    rw [sum_range_succ, ← C_mul_X_pow_eq_monomial, tsub_self, pow_zero, pow_one, map_mul,
      rename_C, rename_X, ← mvpz]
  simp only [add_mul, mul_add]
  -- ⊢ (∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.single x ( …
  rw [add_comm _ (remainder p n)]
  -- ⊢ (∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.single x ( …
  simp only [add_assoc]
  -- ⊢ (∑ x in range (n + 1), ↑(rename (Prod.mk 0)) (↑(monomial (Finsupp.single x ( …
  apply congrArg (Add.add _)
  -- ⊢ ↑p ^ (n + 1) * X (0, n + 1) * ∑ x in range (n + 1), ↑(rename (Prod.mk 1)) (↑ …
  ring
  -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_aux3 WittVector.mul_polyOfInterest_aux3

theorem mul_polyOfInterest_aux4 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * wittMul p (n + 1) =
    -((p : 𝕄) ^ (n + 1) * X (0, n + 1)) * ((p : 𝕄) ^ (n + 1) * X (1, n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (p : 𝕄) ^ (n + 1) * X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)) +
    (remainder p n - wittPolyProdRemainder p (n + 1)) := by
  rw [← add_sub_assoc, eq_sub_iff_add_eq, mul_polyOfInterest_aux2]
  -- ⊢ wittPolyProd p (n + 1) = -(↑p ^ (n + 1) * X (0, n + 1)) * (↑p ^ (n + 1) * X  …
  exact mul_polyOfInterest_aux3 _ _
  -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_aux4 WittVector.mul_polyOfInterest_aux4

theorem mul_polyOfInterest_aux5 (n : ℕ) :
    (p : 𝕄) ^ (n + 1) * polyOfInterest p n = remainder p n - wittPolyProdRemainder p (n + 1) := by
  simp only [polyOfInterest, mul_sub, mul_add, sub_eq_iff_eq_add']
  -- ⊢ ↑p ^ (n + 1) * wittMul p (n + 1) + ↑p ^ (n + 1) * (↑p ^ (n + 1) * X (0, n +  …
  rw [mul_polyOfInterest_aux4 p n]
  -- ⊢ -(↑p ^ (n + 1) * X (0, n + 1)) * (↑p ^ (n + 1) * X (1, n + 1)) + ↑p ^ (n + 1 …
  ring
  -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_aux5 WittVector.mul_polyOfInterest_aux5

theorem mul_polyOfInterest_vars (n : ℕ) :
    ((p : 𝕄) ^ (n + 1) * polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [mul_polyOfInterest_aux5]
  -- ⊢ vars (remainder p n - wittPolyProdRemainder p (n + 1)) ⊆ univ ×ˢ range (n + 1)
  apply Subset.trans (vars_sub_subset _)
  -- ⊢ vars (remainder p n) ∪ vars (wittPolyProdRemainder p (n + 1)) ⊆ univ ×ˢ rang …
  refine' union_subset _ _
  -- ⊢ vars (remainder p n) ⊆ univ ×ˢ range (n + 1)
  · apply remainder_vars
    -- 🎉 no goals
  · apply wittPolyProdRemainder_vars
    -- 🎉 no goals
#align witt_vector.mul_poly_of_interest_vars WittVector.mul_polyOfInterest_vars

theorem polyOfInterest_vars_eq (n : ℕ) : (polyOfInterest p n).vars =
    ((p : 𝕄) ^ (n + 1) * (wittMul p (n + 1) + (p : 𝕄) ^ (n + 1) * X (0, n + 1) * X (1, n + 1) -
      X (0, n + 1) * rename (Prod.mk (1 : Fin 2)) (wittPolynomial p ℤ (n + 1)) -
      X (1, n + 1) * rename (Prod.mk (0 : Fin 2)) (wittPolynomial p ℤ (n + 1)))).vars := by
  have : (p : 𝕄) ^ (n + 1) = C ((p : ℤ) ^ (n + 1)) := by simp only; norm_cast
  -- ⊢ vars (polyOfInterest p n) = vars (↑p ^ (n + 1) * (wittMul p (n + 1) + ↑p ^ ( …
  rw [polyOfInterest, this, vars_C_mul]
  -- ⊢ ↑p ^ (n + 1) ≠ 0
  apply pow_ne_zero
  -- ⊢ ↑p ≠ 0
  exact_mod_cast hp.out.ne_zero
  -- 🎉 no goals
#align witt_vector.poly_of_interest_vars_eq WittVector.polyOfInterest_vars_eq

theorem polyOfInterest_vars (n : ℕ) : (polyOfInterest p n).vars ⊆ univ ×ˢ range (n + 1) := by
  rw [polyOfInterest_vars_eq]; apply mul_polyOfInterest_vars
  -- ⊢ vars (↑p ^ (n + 1) * (wittMul p (n + 1) + ↑p ^ (n + 1) * X (0, n + 1) * X (1 …
                               -- 🎉 no goals
#align witt_vector.poly_of_interest_vars WittVector.polyOfInterest_vars

theorem peval_polyOfInterest (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
    (x * y).coeff (n + 1) + p ^ (n + 1) * x.coeff (n + 1) * y.coeff (n + 1) -
      y.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * x.coeff i ^ p ^ (n + 1 - i) -
      x.coeff (n + 1) * ∑ i in range (n + 1 + 1), p ^ i * y.coeff i ^ p ^ (n + 1 - i) := by
  simp only [polyOfInterest, peval, map_natCast, Matrix.head_cons, map_pow,
    Function.uncurry_apply_pair, aeval_X, Matrix.cons_val_one, map_mul, Matrix.cons_val_zero,
    map_sub]
  rw [sub_sub, add_comm (_ * _), ← sub_sub]
  -- ⊢ ↑(aeval (Function.uncurry ![fun i => coeff x i, fun i => coeff y i])) (wittM …
  have mvpz : (p : MvPolynomial ℕ ℤ) = MvPolynomial.C ↑p := by rw [eq_intCast, Int.cast_ofNat]
  -- ⊢ ↑(aeval (Function.uncurry ![fun i => coeff x i, fun i => coeff y i])) (wittM …
  have : ∀ (f : ℤ →+* k) (g : ℕ → k), eval₂ f g p = f p := by
    intros; rw [mvpz, MvPolynomial.eval₂_C]
  simp [wittPolynomial_eq_sum_C_mul_X_pow, aeval, eval₂_rename, this, mul_coeff, peval, map_natCast,
    map_add, map_pow, map_mul]
#align witt_vector.peval_poly_of_interest WittVector.peval_polyOfInterest

variable [CharP k p]

/-- The characteristic `p` version of `peval_polyOfInterest` -/
theorem peval_polyOfInterest' (n : ℕ) (x y : 𝕎 k) :
    peval (polyOfInterest p n) ![fun i => x.coeff i, fun i => y.coeff i] =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  rw [peval_polyOfInterest]
  -- ⊢ coeff (x * y) (n + 1) + ↑(p ^ (n + 1)) * coeff x (n + 1) * coeff y (n + 1) - …
  have : (p : k) = 0 := CharP.cast_eq_zero k p
  -- ⊢ coeff (x * y) (n + 1) + ↑(p ^ (n + 1)) * coeff x (n + 1) * coeff y (n + 1) - …
  simp only [this, Nat.cast_pow, ne_eq, add_eq_zero, and_false, zero_pow', zero_mul, add_zero]
  -- ⊢ coeff (x * y) (n + 1) - coeff y (n + 1) * ∑ x_1 in range (n + 1 + 1), 0 ^ x_ …
  have sum_zero_pow_mul_pow_p : ∀ y : 𝕎 k, ∑ x : ℕ in range (n + 1 + 1),
      (0 : k) ^ x * y.coeff x ^ p ^ (n + 1 - x) = y.coeff 0 ^ p ^ (n + 1) := by
    intro y
    rw [Finset.sum_eq_single_of_mem 0]
    · simp
    · simp
    · intro j _ hj
      simp [zero_pow (zero_lt_iff.mpr hj)]
  congr <;> apply sum_zero_pow_mul_pow_p
  -- ⊢ ∑ x_1 in range (n + 1 + 1), 0 ^ x_1 * coeff x x_1 ^ p ^ (n + 1 - x_1) = coef …
            -- 🎉 no goals
            -- 🎉 no goals
#align witt_vector.peval_poly_of_interest' WittVector.peval_polyOfInterest'

variable (k)

theorem nth_mul_coeff' (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, f (truncateFun (n + 1) x) (truncateFun (n + 1) y) =
      (x * y).coeff (n + 1) - y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) -
        x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) := by
  simp only [← peval_polyOfInterest']
  -- ⊢ ∃ f, ∀ (x y : 𝕎 k), f (truncateFun (n + 1) x) (truncateFun (n + 1) y) = peva …
  obtain ⟨f₀, hf₀⟩ := exists_restrict_to_vars k (polyOfInterest_vars p n)
  -- ⊢ ∃ f, ∀ (x y : 𝕎 k), f (truncateFun (n + 1) x) (truncateFun (n + 1) y) = peva …
  have : ∀ (a : Multiset (Fin 2)) (b : Multiset ℕ), a ×ˢ b = a.product b := fun a b => rfl
  -- ⊢ ∃ f, ∀ (x y : 𝕎 k), f (truncateFun (n + 1) x) (truncateFun (n + 1) y) = peva …
  let f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k := by
    intro x y
    apply f₀
    rintro ⟨a, ha⟩
    apply Function.uncurry ![x, y]
    simp_rw [product_val, this, Multiset.mem_product, mem_univ_val, true_and_iff, range_val,
      Multiset.range_succ, Multiset.mem_cons, Multiset.mem_range] at ha
    refine' ⟨a.fst, ⟨a.snd, _⟩⟩
    cases' ha with ha ha <;> linarith only [ha]
  use f
  -- ⊢ ∀ (x y : 𝕎 k), f (truncateFun (n + 1) x) (truncateFun (n + 1) y) = peval (po …
  intro x y
  -- ⊢ f (truncateFun (n + 1) x) (truncateFun (n + 1) y) = peval (polyOfInterest p  …
  dsimp [peval]
  -- ⊢ (f₀ fun a => Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] …
  rw [← hf₀]
  -- ⊢ (f₀ fun a => Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] …
  congr
  -- ⊢ (fun a => Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] (↑ …
  ext a
  -- ⊢ Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] (↑a).fst { v …
  cases' a with a ha
  -- ⊢ Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] (↑{ val := a …
  cases' a with i m
  -- ⊢ Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] (↑{ val := ( …
  fin_cases i <;> rfl -- surely this case split is not necessary
  -- ⊢ Matrix.vecCons (truncateFun (n + 1) x) ![truncateFun (n + 1) y] (↑{ val := ( …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align witt_vector.nth_mul_coeff' WittVector.nth_mul_coeff'

theorem nth_mul_coeff (n : ℕ) :
    ∃ f : TruncatedWittVector p (n + 1) k → TruncatedWittVector p (n + 1) k → k,
    ∀ x y : 𝕎 k, (x * y).coeff (n + 1) =
      x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
      f (truncateFun (n + 1) x) (truncateFun (n + 1) y) := by
  obtain ⟨f, hf⟩ := nth_mul_coeff' p k n
  -- ⊢ ∃ f, ∀ (x y : 𝕎 k), coeff (x * y) (n + 1) = coeff x (n + 1) * coeff y 0 ^ p  …
  use f
  -- ⊢ ∀ (x y : 𝕎 k), coeff (x * y) (n + 1) = coeff x (n + 1) * coeff y 0 ^ p ^ (n  …
  intro x y
  -- ⊢ coeff (x * y) (n + 1) = coeff x (n + 1) * coeff y 0 ^ p ^ (n + 1) + coeff y  …
  rw [hf x y]
  -- ⊢ coeff (x * y) (n + 1) = coeff x (n + 1) * coeff y 0 ^ p ^ (n + 1) + coeff y  …
  ring
  -- 🎉 no goals
#align witt_vector.nth_mul_coeff WittVector.nth_mul_coeff

variable {k}

/--
Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
def nthRemainder (n : ℕ) : (Fin (n + 1) → k) → (Fin (n + 1) → k) → k :=
  Classical.choose (nth_mul_coeff p k n)
#align witt_vector.nth_remainder WittVector.nthRemainder

theorem nthRemainder_spec (n : ℕ) (x y : 𝕎 k) : (x * y).coeff (n + 1) =
    x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n + 1) * x.coeff 0 ^ p ^ (n + 1) +
    nthRemainder p n (truncateFun (n + 1) x) (truncateFun (n + 1) y) :=
  Classical.choose_spec (nth_mul_coeff p k n) _ _
#align witt_vector.nth_remainder_spec WittVector.nthRemainder_spec

end WittVector
