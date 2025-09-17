/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/


noncomputable section

open Finsupp Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}
variable [Semiring R] {p q r : R[X]}

section Coeff

@[simp]
theorem coeff_add (p q : R[X]) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp_rw [← ofFinsupp_add, coeff]
  exact Finsupp.add_apply _ _ _

@[simp]
theorem coeff_smul [SMulZeroClass S R] (r : S) (p : R[X]) (n : ℕ) :
    coeff (r • p) n = r • coeff p n := by
  rfl

theorem support_smul [SMulZeroClass S R] (r : S) (p : R[X]) :
    support (r • p) ⊆ support p := by
  intro i hi
  rw [mem_support_iff] at hi ⊢
  contrapose! hi
  simp [hi]

open scoped Pointwise in
theorem card_support_mul_le : #(p * q).support ≤ #p.support * #q.support := by
  calc #(p * q).support
    _ = #(p.toFinsupp * q.toFinsupp).support := by rw [← support_toFinsupp, toFinsupp_mul]
    _ ≤ #(p.toFinsupp.support + q.toFinsupp.support) :=
      Finset.card_le_card (AddMonoidAlgebra.support_mul p.toFinsupp q.toFinsupp)
    _ ≤ #p.support * #q.support := Finset.card_image₂_le ..

/-- `Polynomial.sum` as a linear map. -/
@[simps]
def lsum {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : ℕ → A →ₗ[R] M) : A[X] →ₗ[R] M where
  toFun p := p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    rw [sum_eq_of_subset (f · ·) (fun n => (f n).map_zero) (support_smul c p)]
    simp only [sum_def, Finset.smul_sum, coeff_smul, LinearMap.map_smul, RingHom.id_apply]

variable (R) in
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : R[X] →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

@[simp]
theorem lcoeff_apply (n : ℕ) (f : R[X]) : lcoeff R n f = coeff f n :=
  rfl

@[simp]
theorem finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    coeff (∑ b ∈ s, f b) n = ∑ b ∈ s, coeff (f b) n :=
  map_sum (lcoeff R n) _ _

lemma coeff_list_sum (l : List R[X]) (n : ℕ) :
    l.sum.coeff n = (l.map (lcoeff R n)).sum :=
  map_list_sum (lcoeff R n) _

lemma coeff_list_sum_map {ι : Type*} (l : List ι) (f : ι → R[X]) (n : ℕ) :
    (l.map f).sum.coeff n = (l.map (fun a => (f a).coeff n)).sum := by
  simp_rw [coeff_list_sum, List.map_map, Function.comp_def, lcoeff_apply]

@[simp]
theorem coeff_sum [Semiring S] (n : ℕ) (f : ℕ → R → S[X]) :
    coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n := by
  rcases p with ⟨⟩
  simp [Polynomial.sum, support_ofFinsupp, coeff_ofFinsupp]

/-- Decomposes the coefficient of the product `p * q` as a sum
over `antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem coeff_mul (p q : R[X]) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_apply_antidiagonal p q n _ Finset.mem_antidiagonal

@[simp]
theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by simp [coeff_mul]

theorem mul_coeff_one (p q : R[X]) :
    coeff (p * q) 1 = coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0 := by
  rw [coeff_mul, Nat.antidiagonal_eq_map]
  simp [sum_range_succ]

/-- `constantCoeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
@[simps]
def constantCoeff : R[X] →+* R where
  toFun p := coeff p 0
  map_one' := coeff_one_zero
  map_mul' := mul_coeff_zero
  map_zero' := coeff_zero 0
  map_add' p q := coeff_add p q 0

lemma constantCoeff_surjective : Function.Surjective (constantCoeff (R := R)) :=
  fun x ↦ ⟨C x, by simp⟩

theorem isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x :=
  ⟨fun h => (congr_arg IsUnit coeff_C_zero).mp (h.map <| @constantCoeff R _), fun h => h.map C⟩

theorem coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by simp

theorem coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by simp

theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff (C x * X ^ k : R[X]) n = if n = k then x else 0 := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  congr 1
  simp [eq_comm]

theorem coeff_C_mul_X (x : R) (n : ℕ) : coeff (C x * X : R[X]) n = if n = 1 then x else 0 := by
  rw [← pow_one X, coeff_C_mul_X_pow]

@[simp]
theorem coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n := by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.single_zero_mul_apply p a n

theorem C_mul' (a : R) (f : R[X]) : C a * f = a • f := by
  ext
  rw [coeff_C_mul, coeff_smul, smul_eq_mul]

@[simp]
theorem coeff_mul_C (p : R[X]) (n : ℕ) (a : R) : coeff (p * C a) n = coeff p n * a := by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_single_zero_apply p a n

@[simp] lemma coeff_mul_natCast {a k : ℕ} :
    coeff (p * (a : R[X])) k = coeff p k * (↑a : R) := coeff_mul_C _ _ _

@[simp] lemma coeff_natCast_mul {a k : ℕ} :
    coeff ((a : R[X]) * p) k = a * coeff p k := coeff_C_mul _

@[simp] lemma coeff_mul_ofNat {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff (p * (ofNat(a) : R[X])) k = coeff p k * ofNat(a) := coeff_mul_C _ _ _

@[simp] lemma coeff_ofNat_mul {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff ((ofNat(a) : R[X]) * p) k = ofNat(a) * coeff p k := coeff_C_mul _

@[simp] lemma coeff_mul_intCast [Ring S] {p : S[X]} {a : ℤ} {k : ℕ} :
    coeff (p * (a : S[X])) k = coeff p k * (↑a : S) := coeff_mul_C _ _ _

@[simp] lemma coeff_intCast_mul [Ring S] {p : S[X]} {a : ℤ} {k : ℕ} :
    coeff ((a : S[X]) * p) k = a * coeff p k := coeff_C_mul _

@[simp]
theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [one_mul, RingHom.map_one, ← coeff_C_mul_X_pow]

theorem coeff_X_pow_self (n : ℕ) : coeff (X ^ n : R[X]) n = 1 := by simp

section Fewnomials

open Finset

theorem support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    support (C x * X ^ k + C y * X ^ m) = {k, m} := by
  apply subset_antisymm (support_binomial' k m x y)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm, mul_zero, zero_add,
    add_zero, Ne, hx, hy, not_false_eq_true, and_true]

theorem support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) = {k, m, n} := by
  apply subset_antisymm (support_trinomial' k m n x y z)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', mul_zero, add_zero,
    zero_add, Ne, hx, hy, hz, not_false_eq_true, and_true]

theorem card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    #(support (C x * X ^ k + C y * X ^ m)) = 2 := by
  rw [support_binomial h hx hy, card_insert_of_notMem (mt mem_singleton.mp h), card_singleton]

theorem card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) : #(support (C x * X ^ k + C y * X ^ m + C z * X ^ n)) = 3 := by
  rw [support_trinomial hkm hmn hx hy hz,
    card_insert_of_notMem
      (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
    card_insert_of_notMem (mt mem_singleton.mp hmn.ne), card_singleton]

end Fewnomials

@[simp]
theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) :
    coeff (p * Polynomial.X ^ n) (d + n) = coeff p d := by
  rw [coeff_mul, Finset.sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_one]
  all_goals grind [mem_antidiagonal, coeff_X_pow, mul_zero]

@[simp]
theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) :
    coeff (Polynomial.X ^ n * p) (d + n) = coeff p d := by
  rw [(commute_X_pow p n).eq, coeff_mul_X_pow]

theorem coeff_mul_X_pow' (p : R[X]) (n d : ℕ) :
    (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

theorem coeff_X_pow_mul' (p : R[X]) (n d : ℕ) :
    (X ^ n * p).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  rw [(commute_X_pow p n).eq, coeff_mul_X_pow']

@[simp]
theorem coeff_mul_X (p : R[X]) (n : ℕ) : coeff (p * X) (n + 1) = coeff p n := by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp]
theorem coeff_X_mul (p : R[X]) (n : ℕ) : coeff (X * p) (n + 1) = coeff p n := by
  rw [(commute_X p).eq, coeff_mul_X]

theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) :
    coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : R[X]) (n d : ℕ) (r : R) :
    coeff (monomial n r * p) (d + n) = r * coeff p d := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) :
    coeff (p * monomial 0 r) d = coeff p d * r :=
  coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) :
    coeff (monomial 0 r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r

theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ} (H : p * X ^ n = 0) : p = 0 :=
  ext fun k => (coeff_mul_X_pow p n k).symm.trans <| ext_iff.1 H (k + n)

theorem isRegular_X_pow (n : ℕ) : IsRegular (X ^ n : R[X]) := by
  suffices IsLeftRegular (X^n : R[X]) from
    ⟨this, this.right_of_commute (fun p => commute_X_pow p n)⟩
  intro P Q (hPQ : X^n * P = X^n * Q)
  ext i
  rw [← coeff_X_pow_mul P n i, hPQ, coeff_X_pow_mul Q n i]

@[simp] theorem isRegular_X : IsRegular (X : R[X]) := pow_one (X : R[X]) ▸ isRegular_X_pow 1

theorem coeff_X_add_C_pow (r : R) (n k : ℕ) :
    ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, ← C_eq_natCast, ← C_pow, coeff_mul_C]
  rw [Finset.sum_eq_single k, coeff_X_pow_self, one_mul]
  · intro _ _ h
    simp [coeff_X_pow, h.symm]
  · simp only [coeff_X_pow_self, one_mul, not_lt, Finset.mem_range]
    intro h
    rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

theorem coeff_X_add_one_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((X + 1) ^ n).coeff k = (n.choose k : R) := by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]

theorem coeff_one_add_X_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((1 + X) ^ n).coeff k = (n.choose k : R) := by rw [add_comm _ X, coeff_X_add_one_pow]

theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose c hc using h
    classical
      let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
      let ψ : R[X] := ∑ i ∈ φ.support, monomial i (c' i)
      use ψ
      ext i
      simp only [c', ψ, coeff_C_mul, mem_support_iff, coeff_monomial, finset_sum_coeff,
        Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [Classical.not_not] at hi
        rwa [mul_zero]

theorem smul_eq_C_mul (a : R) : a • p = C a * p := by simp [ext_iff]

theorem update_eq_add_sub_coeff {R : Type*} [Ring R] (p : R[X]) (n : ℕ) (a : R) :
    p.update n a = p + Polynomial.C (a - p.coeff n) * Polynomial.X ^ n := by
  ext
  rw [coeff_update_apply, coeff_add, coeff_C_mul_X_pow]
  split_ifs with h <;> simp [h]

end Coeff

section cast

theorem natCast_coeff_zero {n : ℕ} {R : Type*} [Semiring R] : (n : R[X]).coeff 0 = n := by
  simp only [coeff_natCast_ite, ite_true]

@[norm_cast]
theorem natCast_inj {m n : ℕ} {R : Type*} [Semiring R] [CharZero R] :
    (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

@[simp]
theorem intCast_coeff_zero {i : ℤ} {R : Type*} [Ring R] : (i : R[X]).coeff 0 = i := by
  cases i <;> simp

@[norm_cast]
theorem intCast_inj {m n : ℤ} {R : Type*} [Ring R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

end cast

instance charZero [CharZero R] : CharZero R[X] where cast_injective _x _y := natCast_inj.mp

instance charP {p : ℕ} [CharP R p] : CharP R[X] p where
  cast_eq_zero_iff n := by
    rw [← CharP.cast_eq_zero_iff R, ← C_inj (R := R), map_natCast, C_0]

end Polynomial
