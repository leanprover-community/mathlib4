/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Regular.Pow

#align_import data.polynomial.coeff from "leanprover-community/mathlib"@"2651125b48fc5c170ab1111afd0817c903b1fc6c"

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/


set_option linter.uppercaseLean3 false

noncomputable section

open Finsupp Finset AddMonoidAlgebra

open BigOperators Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

section Coeff

theorem coeff_one (n : ℕ) : coeff (1 : R[X]) n = if 0 = n then 1 else 0 :=
  coeff_monomial
#align polynomial.coeff_one Polynomial.coeff_one

@[simp]
theorem coeff_add (p q : R[X]) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  rcases p with ⟨⟩
  -- ⊢ coeff ({ toFinsupp := toFinsupp✝ } + q) n = coeff { toFinsupp := toFinsupp✝  …
  rcases q with ⟨⟩
  -- ⊢ coeff ({ toFinsupp := toFinsupp✝¹ } + { toFinsupp := toFinsupp✝ }) n = coeff …
  simp_rw [← ofFinsupp_add, coeff]
  -- ⊢ ↑(toFinsupp✝¹ + toFinsupp✝) n = ↑toFinsupp✝¹ n + ↑toFinsupp✝ n
  exact Finsupp.add_apply _ _ _
  -- 🎉 no goals
#align polynomial.coeff_add Polynomial.coeff_add

set_option linter.deprecated false in
@[simp]
theorem coeff_bit0 (p : R[X]) (n : ℕ) : coeff (bit0 p) n = bit0 (coeff p n) := by simp [bit0]
                                                                                  -- 🎉 no goals
#align polynomial.coeff_bit0 Polynomial.coeff_bit0

@[simp]
theorem coeff_smul [SMulZeroClass S R] (r : S) (p : R[X]) (n : ℕ) :
    coeff (r • p) n = r • coeff p n := by
  rcases p with ⟨⟩
  -- ⊢ coeff (r • { toFinsupp := toFinsupp✝ }) n = r • coeff { toFinsupp := toFinsu …
  simp_rw [← ofFinsupp_smul, coeff]
  -- ⊢ ↑(r • toFinsupp✝) n = r • ↑toFinsupp✝ n
  exact Finsupp.smul_apply _ _ _
  -- 🎉 no goals
#align polynomial.coeff_smul Polynomial.coeff_smul

theorem support_smul [Monoid S] [DistribMulAction S R] (r : S) (p : R[X]) :
    support (r • p) ⊆ support p := by
  intro i hi
  -- ⊢ i ∈ support p
  simp [mem_support_iff] at hi ⊢
  -- ⊢ ¬coeff p i = 0
  contrapose! hi
  -- ⊢ r • coeff p i = 0
  simp [hi]
  -- 🎉 no goals
#align polynomial.support_smul Polynomial.support_smul

/-- `Polynomial.sum` as a linear map. -/
@[simps]
def lsum {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : ℕ → A →ₗ[R] M) : A[X] →ₗ[R] M
    where
  toFun p := p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    -- Porting note: `dsimp only []` is required for beta reduction.
    dsimp only []
    -- ⊢ (sum (c • p) fun x x_1 => ↑(f x) x_1) = ↑(RingHom.id R) c • sum p fun x x_1  …
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    -- ⊢ ∑ n in support p, ↑(f n) (coeff (c • p) n) = ↑(RingHom.id R) c • sum p fun x …
    simp only [sum_def, Finset.smul_sum, coeff_smul, LinearMap.map_smul, RingHom.id_apply]
    -- 🎉 no goals
#align polynomial.lsum Polynomial.lsum
#align polynomial.lsum_apply Polynomial.lsum_apply

variable (R)

/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : R[X] →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n
#align polynomial.lcoeff Polynomial.lcoeff

variable {R}

@[simp]
theorem lcoeff_apply (n : ℕ) (f : R[X]) : lcoeff R n f = coeff f n :=
  rfl
#align polynomial.lcoeff_apply Polynomial.lcoeff_apply

@[simp]
theorem finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
  (lcoeff R n).map_sum
#align polynomial.finset_sum_coeff Polynomial.finset_sum_coeff

theorem coeff_sum [Semiring S] (n : ℕ) (f : ℕ → R → S[X]) :
    coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n := by
  rcases p with ⟨⟩
  -- ⊢ coeff (sum { toFinsupp := toFinsupp✝ } f) n = sum { toFinsupp := toFinsupp✝  …
  -- Porting note: Was `simp [Polynomial.sum, support, coeff]`.
  simp [Polynomial.sum, support_ofFinsupp, coeff_ofFinsupp]
  -- 🎉 no goals
#align polynomial.coeff_sum Polynomial.coeff_sum

/-- Decomposes the coefficient of the product `p * q` as a sum
over `Nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem coeff_mul (p q : R[X]) (n : ℕ) :
    coeff (p * q) n = ∑ x in Nat.antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  -- ⊢ coeff ({ toFinsupp := p } * q) n = ∑ x in Nat.antidiagonal n, coeff { toFins …
                     -- ⊢ coeff ({ toFinsupp := p } * { toFinsupp := q }) n = ∑ x in Nat.antidiagonal  …
  simp_rw [← ofFinsupp_mul, coeff]
  -- ⊢ ↑(p * q) n = ∑ x in Nat.antidiagonal n, ↑p x.fst * ↑q x.snd
  exact AddMonoidAlgebra.mul_apply_antidiagonal p q n _ Nat.mem_antidiagonal
  -- 🎉 no goals
#align polynomial.coeff_mul Polynomial.coeff_mul

@[simp]
theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by simp [coeff_mul]
                                                                                    -- 🎉 no goals
#align polynomial.mul_coeff_zero Polynomial.mul_coeff_zero

/-- `constantCoeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
@[simps]
def constantCoeff : R[X] →+* R where
  toFun p := coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0
#align polynomial.constant_coeff Polynomial.constantCoeff
#align polynomial.constant_coeff_apply Polynomial.constantCoeff_apply

theorem isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x :=
  ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @constantCoeff R _), fun h => h.map C⟩
#align polynomial.is_unit_C Polynomial.isUnit_C

theorem coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by simp
                                                                -- 🎉 no goals
#align polynomial.coeff_mul_X_zero Polynomial.coeff_mul_X_zero

theorem coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by simp
                                                                -- 🎉 no goals
#align polynomial.coeff_X_mul_zero Polynomial.coeff_X_mul_zero

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff (C x * X ^ k : R[X]) n = if n = k then x else 0 := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  -- ⊢ (if k = n then x else 0) = if n = k then x else 0
  congr 1
  -- ⊢ (k = n) = (n = k)
  simp [eq_comm]
  -- 🎉 no goals
#align polynomial.coeff_C_mul_X_pow Polynomial.coeff_C_mul_X_pow

theorem coeff_C_mul_X (x : R) (n : ℕ) : coeff (C x * X : R[X]) n = if n = 1 then x else 0 := by
  rw [← pow_one X, coeff_C_mul_X_pow]
  -- 🎉 no goals
#align polynomial.coeff_C_mul_X Polynomial.coeff_C_mul_X

@[simp]
theorem coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n := by
  rcases p with ⟨p⟩
  -- ⊢ coeff (↑C a * { toFinsupp := p }) n = a * coeff { toFinsupp := p } n
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  -- ⊢ ↑(Finsupp.single 0 a * p) n = a * ↑p n
  exact AddMonoidAlgebra.single_zero_mul_apply p a n
  -- 🎉 no goals
#align polynomial.coeff_C_mul Polynomial.coeff_C_mul

theorem C_mul' (a : R) (f : R[X]) : C a * f = a • f := by
  ext
  -- ⊢ coeff (↑C a * f) n✝ = coeff (a • f) n✝
  rw [coeff_C_mul, coeff_smul, smul_eq_mul]
  -- 🎉 no goals
#align polynomial.C_mul' Polynomial.C_mul'

@[simp]
theorem coeff_mul_C (p : R[X]) (n : ℕ) (a : R) : coeff (p * C a) n = coeff p n * a := by
  rcases p with ⟨p⟩
  -- ⊢ coeff ({ toFinsupp := p } * ↑C a) n = coeff { toFinsupp := p } n * a
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  -- ⊢ ↑(p * Finsupp.single 0 a) n = ↑p n * a
  exact AddMonoidAlgebra.mul_single_zero_apply p a n
  -- 🎉 no goals
#align polynomial.coeff_mul_C Polynomial.coeff_mul_C

@[simp]
theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [one_mul, RingHom.map_one, ← coeff_C_mul_X_pow]
  -- 🎉 no goals
#align polynomial.coeff_X_pow Polynomial.coeff_X_pow

theorem coeff_X_pow_self (n : ℕ) : coeff (X ^ n : R[X]) n = 1 := by simp
                                                                    -- 🎉 no goals
#align polynomial.coeff_X_pow_self Polynomial.coeff_X_pow_self

section Fewnomials

open Finset

theorem support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    support (C x * X ^ k + C y * X ^ m) = {k, m} := by
  apply subset_antisymm (support_binomial' k m x y)
  -- ⊢ {k, m} ⊆ support (↑C x * X ^ k + ↑C y * X ^ m)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne.def, hx, hy]
#align polynomial.support_binomial Polynomial.support_binomial

theorem support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) = {k, m, n} := by
  apply subset_antisymm (support_trinomial' k m n x y z)
  -- ⊢ {k, m, n} ⊆ support (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', mul_zero, add_zero,
    zero_add, Ne.def, hx, hy, hz]
#align polynomial.support_trinomial Polynomial.support_trinomial

theorem card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    card (support (C x * X ^ k + C y * X ^ m)) = 2 := by
  rw [support_binomial h hx hy, card_insert_of_not_mem (mt mem_singleton.mp h), card_singleton]
  -- 🎉 no goals
#align polynomial.card_support_binomial Polynomial.card_support_binomial

theorem card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) : card (support (C x * X ^ k + C y * X ^ m + C z * X ^ n)) = 3 := by
  rw [support_trinomial hkm hmn hx hy hz,
    card_insert_of_not_mem
      (mt mem_insert.mp (not_or_of_not hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
    card_insert_of_not_mem (mt mem_singleton.mp hmn.ne), card_singleton]
#align polynomial.card_support_trinomial Polynomial.card_support_trinomial

end Fewnomials

@[simp]
theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) :
    coeff (p * Polynomial.X ^ n) (d + n) = coeff p d := by
  rw [coeff_mul, sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  -- ⊢ ∀ (b : ℕ × ℕ), b ∈ Nat.antidiagonal (d + n) → b ≠ (d, n) → coeff p b.fst * c …
  · rintro ⟨i, j⟩ h1 h2
    -- ⊢ coeff p (i, j).fst * coeff (X ^ n) (i, j).snd = 0
    rw [coeff_X_pow, if_neg, mul_zero]
    -- ⊢ ¬(i, j).snd = n
    rintro rfl
    -- ⊢ False
    apply h2
    -- ⊢ (i, j) = (d, (i, j).snd)
    rw [Nat.mem_antidiagonal, add_right_cancel_iff] at h1
    -- ⊢ (i, j) = (d, (i, j).snd)
    subst h1
    -- ⊢ (i, j) = ((i, j).fst, (i, j).snd)
    rfl
    -- 🎉 no goals
  · exact fun h1 => (h1 (Nat.mem_antidiagonal.2 rfl)).elim
    -- 🎉 no goals
#align polynomial.coeff_mul_X_pow Polynomial.coeff_mul_X_pow

@[simp]
theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) : coeff (Polynomial.X ^ n * p) (d + n) = coeff p d :=
  by rw [(commute_X_pow p n).eq, coeff_mul_X_pow]
     -- 🎉 no goals
#align polynomial.coeff_X_pow_mul Polynomial.coeff_X_pow_mul

theorem coeff_mul_X_pow' (p : R[X]) (n d : ℕ) :
    (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  split_ifs with h
  -- ⊢ coeff (p * X ^ n) d = coeff p (d - n)
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
    -- 🎉 no goals
  · refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
    -- ⊢ coeff p x.fst * coeff (X ^ n) x.snd = 0
    rw [coeff_X_pow, if_neg, mul_zero]
    -- ⊢ ¬x.snd = n
    exact ((le_of_add_le_right (Finset.Nat.mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne
    -- 🎉 no goals
#align polynomial.coeff_mul_X_pow' Polynomial.coeff_mul_X_pow'

theorem coeff_X_pow_mul' (p : R[X]) (n d : ℕ) :
    (X ^ n * p).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  rw [(commute_X_pow p n).eq, coeff_mul_X_pow']
  -- 🎉 no goals
#align polynomial.coeff_X_pow_mul' Polynomial.coeff_X_pow_mul'

@[simp]
theorem coeff_mul_X (p : R[X]) (n : ℕ) : coeff (p * X) (n + 1) = coeff p n := by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n
  -- 🎉 no goals
#align polynomial.coeff_mul_X Polynomial.coeff_mul_X

@[simp]
theorem coeff_X_mul (p : R[X]) (n : ℕ) : coeff (X * p) (n + 1) = coeff p n := by
  rw [(commute_X p).eq, coeff_mul_X]
  -- 🎉 no goals
#align polynomial.coeff_X_mul Polynomial.coeff_X_mul

theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) :
    coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_X_pow]
  -- 🎉 no goals
#align polynomial.coeff_mul_monomial Polynomial.coeff_mul_monomial

theorem coeff_monomial_mul (p : R[X]) (n d : ℕ) (r : R) :
    coeff (monomial n r * p) (d + n) = r * coeff p d := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]
  -- 🎉 no goals
#align polynomial.coeff_monomial_mul Polynomial.coeff_monomial_mul

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) :
    coeff (p * monomial 0 r) d = coeff p d * r :=
  coeff_mul_monomial p 0 d r
#align polynomial.coeff_mul_monomial_zero Polynomial.coeff_mul_monomial_zero

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) :
    coeff (monomial 0 r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r
#align polynomial.coeff_monomial_zero_mul Polynomial.coeff_monomial_zero_mul

theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ} (H : p * X ^ n = 0) : p = 0 :=
  ext fun k => (coeff_mul_X_pow p n k).symm.trans <| ext_iff.1 H (k + n)
#align polynomial.mul_X_pow_eq_zero Polynomial.mul_X_pow_eq_zero

@[simp] theorem isRegular_X : IsRegular (X : R[X]) := by
  suffices : IsLeftRegular (X : R[X])
  -- ⊢ IsRegular X
  · exact ⟨this, this.right_of_commute commute_X⟩
    -- 🎉 no goals
  intro P Q (hPQ : X * P = X * Q)
  -- ⊢ P = Q
  ext i
  -- ⊢ coeff P i = coeff Q i
  rw [← coeff_X_mul P i, hPQ, coeff_X_mul Q i]
  -- 🎉 no goals

-- TODO Unify this with `Polynomial.Monic.isRegular`
theorem isRegular_X_pow (n : ℕ) : IsRegular (X ^ n : R[X]) := isRegular_X.pow n

theorem coeff_X_add_C_pow (r : R) (n k : ℕ) :
    ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, LinearMap.map_sum]
  -- ⊢ ∑ i in range (n + 1), ↑(lcoeff R k) (X ^ i * ↑C r ^ (n - i) * ↑(Nat.choose n …
  simp only [one_pow, mul_one, lcoeff_apply, ← C_eq_nat_cast, ← C_pow, coeff_mul_C, Nat.cast_id]
  -- ⊢ ∑ x in range (n + 1), coeff (X ^ x) k * r ^ (n - x) * ↑(Nat.choose n x) = r  …
  rw [Finset.sum_eq_single k, coeff_X_pow_self, one_mul]
  -- ⊢ ∀ (b : ℕ), b ∈ range (n + 1) → b ≠ k → coeff (X ^ b) k * r ^ (n - b) * ↑(Nat …
  · intro _ _ h
    -- ⊢ coeff (X ^ b✝) k * r ^ (n - b✝) * ↑(Nat.choose n b✝) = 0
    simp [coeff_X_pow, h.symm]
    -- 🎉 no goals
  · simp only [coeff_X_pow_self, one_mul, not_lt, Finset.mem_range]
    -- ⊢ n + 1 ≤ k → r ^ (n - k) * ↑(Nat.choose n k) = 0
    intro h
    -- ⊢ r ^ (n - k) * ↑(Nat.choose n k) = 0
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]
    -- 🎉 no goals
#align polynomial.coeff_X_add_C_pow Polynomial.coeff_X_add_C_pow

theorem coeff_X_add_one_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((X + 1) ^ n).coeff k = (n.choose k : R) := by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]
                                                   -- 🎉 no goals
#align polynomial.coeff_X_add_one_pow Polynomial.coeff_X_add_one_pow

theorem coeff_one_add_X_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((1 + X) ^ n).coeff k = (n.choose k : R) := by rw [add_comm _ X, coeff_X_add_one_pow]
                                                   -- 🎉 no goals
#align polynomial.coeff_one_add_X_pow Polynomial.coeff_one_add_X_pow

theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  -- ⊢ ↑C r ∣ φ → ∀ (i : ℕ), r ∣ coeff φ i
  · rintro ⟨φ, rfl⟩ c
    -- ⊢ r ∣ coeff (↑C r * φ) c
    rw [coeff_C_mul]
    -- ⊢ r ∣ r * coeff φ c
    apply dvd_mul_right
    -- 🎉 no goals
  · intro h
    -- ⊢ ↑C r ∣ φ
    choose c hc using h
    -- ⊢ ↑C r ∣ φ
    classical
      let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
      let ψ : R[X] := ∑ i in φ.support, monomial i (c' i)
      use ψ
      ext i
      simp only [coeff_C_mul, mem_support_iff, coeff_monomial, finset_sum_coeff,
        Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [Classical.not_not] at hi
        rwa [mul_zero]
#align polynomial.C_dvd_iff_dvd_coeff Polynomial.C_dvd_iff_dvd_coeff

set_option linter.deprecated false in
theorem coeff_bit0_mul (P Q : R[X]) (n : ℕ) : coeff (bit0 P * Q) n = 2 * coeff (P * Q) n := by
  -- Porting note: `two_mul` is required.
  simp [bit0, add_mul, two_mul]
  -- 🎉 no goals
#align polynomial.coeff_bit0_mul Polynomial.coeff_bit0_mul

set_option linter.deprecated false in
theorem coeff_bit1_mul (P Q : R[X]) (n : ℕ) :
    coeff (bit1 P * Q) n = 2 * coeff (P * Q) n + coeff Q n := by
  simp [bit1, add_mul, coeff_bit0_mul]
  -- 🎉 no goals
#align polynomial.coeff_bit1_mul Polynomial.coeff_bit1_mul

theorem smul_eq_C_mul (a : R) : a • p = C a * p := by simp [ext_iff]
                                                      -- 🎉 no goals
#align polynomial.smul_eq_C_mul Polynomial.smul_eq_C_mul

theorem update_eq_add_sub_coeff {R : Type*} [Ring R] (p : R[X]) (n : ℕ) (a : R) :
    p.update n a = p + Polynomial.C (a - p.coeff n) * Polynomial.X ^ n := by
  ext
  -- ⊢ coeff (update p n a) n✝ = coeff (p + ↑C (a - coeff p n) * X ^ n) n✝
  rw [coeff_update_apply, coeff_add, coeff_C_mul_X_pow]
  -- ⊢ (if n✝ = n then a else coeff p n✝) = coeff p n✝ + if n✝ = n then a - coeff p …
  split_ifs with h <;> simp [h]
  -- ⊢ a = coeff p n✝ + (a - coeff p n)
                       -- 🎉 no goals
                       -- 🎉 no goals
#align polynomial.update_eq_add_sub_coeff Polynomial.update_eq_add_sub_coeff

end Coeff

section cast

theorem nat_cast_coeff_zero {n : ℕ} {R : Type*} [Semiring R] : (n : R[X]).coeff 0 = n := by
  simp only [coeff_nat_cast_ite, ite_true]
  -- 🎉 no goals
#align polynomial.nat_cast_coeff_zero Polynomial.nat_cast_coeff_zero

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem nat_cast_inj {m n : ℕ} {R : Type*} [Semiring R] [CharZero R] :
    (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  -- ⊢ ↑m = ↑n → m = n
  · intro h
    -- ⊢ m = n
    apply_fun fun p => p.coeff 0 at h
    -- ⊢ m = n
    simpa using h
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ ↑m = ↑m
    rfl
    -- 🎉 no goals
#align polynomial.nat_cast_inj Polynomial.nat_cast_inj

@[simp]
theorem int_cast_coeff_zero {i : ℤ} {R : Type*} [Ring R] : (i : R[X]).coeff 0 = i := by
  cases i <;> simp
  -- ⊢ coeff (↑(Int.ofNat a✝)) 0 = ↑(Int.ofNat a✝)
              -- 🎉 no goals
              -- 🎉 no goals
#align polynomial.int_cast_coeff_zero Polynomial.int_cast_coeff_zero

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem int_cast_inj {m n : ℤ} {R : Type*} [Ring R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  -- ⊢ ↑m = ↑n → m = n
  · intro h
    -- ⊢ m = n
    apply_fun fun p => p.coeff 0 at h
    -- ⊢ m = n
    simpa using h
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ ↑m = ↑m
    rfl
    -- 🎉 no goals
#align polynomial.int_cast_inj Polynomial.int_cast_inj

end cast

instance charZero [CharZero R] : CharZero R[X] where cast_injective _x _y := nat_cast_inj.mp
#align polynomial.char_zero Polynomial.charZero

end Polynomial
