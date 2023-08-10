/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Hom.Iterate
import Mathlib.Data.Polynomial.Eval

#align_import data.polynomial.derivative from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# The derivative map on polynomials

## Main definitions
 * `Polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.

-/


noncomputable section

open Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section Derivative

section Semiring

variable [Semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
  map_add' p q := by
    dsimp only
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, RingHom.map_add, eq_self_iff_true, zero_mul,
        RingHom.map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, coeff_C_mul, RingHom.map_mul, forall_const, zero_mul,
        RingHom.map_zero, sum]
#align polynomial.derivative Polynomial.derivative

theorem derivative_apply (p : R[X]) : derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1) :=
  rfl
#align polynomial.derivative_apply Polynomial.derivative_apply

theorem coeff_derivative (p : R[X]) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (n + 1) := by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum, Finset.sum_eq_single (n + 1)]
  simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true, eq_self_iff_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero, mul_zero, zero_mul]
    · intro _ H
      rw [Nat.succ_sub_one, if_neg (mt (congr_arg Nat.succ) H.symm), mul_zero]
  · rw [if_pos (add_tsub_cancel_right n 1).symm, mul_one, Nat.cast_add, Nat.cast_one,
      mem_support_iff]
    intro h
    push_neg at h
    simp [h]
#align polynomial.coeff_derivative Polynomial.coeff_derivative

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_zero : derivative (0 : R[X]) = 0 :=
  derivative.map_zero
#align polynomial.derivative_zero Polynomial.derivative_zero

@[simp]
theorem iterate_derivative_zero {k : ℕ} : derivative^[k] (0 : R[X]) = 0 := by
  induction' k with k ih
  · simp
  · simp [ih]
#align polynomial.iterate_derivative_zero Polynomial.iterate_derivative_zero

@[simp]
theorem derivative_monomial (a : R) (n : ℕ) :
    derivative (monomial n a) = monomial (n - 1) (a * n) := by
  rw [derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial]
  simp
#align polynomial.derivative_monomial Polynomial.derivative_monomial

theorem derivative_C_mul_X (a : R) : derivative (C a * X) = C a := by
  simp [C_mul_X_eq_monomial, derivative_monomial, Nat.cast_one, mul_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_C_mul_X Polynomial.derivative_C_mul_X

theorem derivative_C_mul_X_pow (a : R) (n : ℕ) :
    derivative (C a * X ^ n) = C (a * n) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_C_mul_X_pow Polynomial.derivative_C_mul_X_pow

theorem derivative_C_mul_X_sq (a : R) : derivative (C a * X ^ 2) = C (a * 2) * X := by
  rw [derivative_C_mul_X_pow, Nat.cast_two, pow_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_C_mul_X_sq Polynomial.derivative_C_mul_X_sq

@[simp]
theorem derivative_X_pow (n : ℕ) : derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1) := by
  convert derivative_C_mul_X_pow (1 : R) n <;> simp
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_pow Polynomial.derivative_X_pow

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_X_sq : derivative (X ^ 2 : R[X]) = C 2 * X := by
  rw [derivative_X_pow, Nat.cast_two, pow_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_sq Polynomial.derivative_X_sq

@[simp]
theorem derivative_C {a : R} : derivative (C a) = 0 := by simp [derivative_apply]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_C Polynomial.derivative_C

theorem derivative_of_natDegree_zero {p : R[X]} (hp : p.natDegree = 0) : derivative p = 0 := by
  rw [eq_C_of_natDegree_eq_zero hp, derivative_C]
#align polynomial.derivative_of_nat_degree_zero Polynomial.derivative_of_natDegree_zero

@[simp]
theorem derivative_X : derivative (X : R[X]) = 1 :=
  (derivative_monomial _ _).trans <| by simp
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X Polynomial.derivative_X

@[simp]
theorem derivative_one : derivative (1 : R[X]) = 0 :=
  derivative_C
#align polynomial.derivative_one Polynomial.derivative_one

set_option linter.deprecated false in
--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_bit0 {a : R[X]} : derivative (bit0 a) = bit0 (derivative a) := by simp [bit0]
#align polynomial.derivative_bit0 Polynomial.derivative_bit0

set_option linter.deprecated false in
--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_bit1 {a : R[X]} : derivative (bit1 a) = bit0 (derivative a) := by simp [bit1]
#align polynomial.derivative_bit1 Polynomial.derivative_bit1

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_add {f g : R[X]} : derivative (f + g) = derivative f + derivative g :=
  derivative.map_add f g
#align polynomial.derivative_add Polynomial.derivative_add

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_X_add_C (c : R) : derivative (X + C c) = 1 := by
  rw [derivative_add, derivative_X, derivative_C, add_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_add_C Polynomial.derivative_X_add_C

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_sum {s : Finset ι} {f : ι → R[X]} :
    derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
  derivative.map_sum
#align polynomial.derivative_sum Polynomial.derivative_sum

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_smul {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (s : S)
    (p : R[X]) : derivative (s • p) = s • derivative p :=
  derivative.map_smul_of_tower s p
#align polynomial.derivative_smul Polynomial.derivative_smul

@[simp]
theorem iterate_derivative_smul {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    (s : S) (p : R[X]) (k : ℕ) : derivative^[k] (s • p) = s • derivative^[k] p := by
  induction' k with k ih generalizing p
  · simp
  · simp [ih]
#align polynomial.iterate_derivative_smul Polynomial.iterate_derivative_smul

@[simp]
theorem iterate_derivative_C_mul (a : R) (p : R[X]) (k : ℕ) :
    derivative^[k] (C a * p) = C a * derivative^[k] p := by
  simp_rw [← smul_eq_C_mul, iterate_derivative_smul]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_C_mul Polynomial.iterate_derivative_C_mul

theorem of_mem_support_derivative {p : R[X]} {n : ℕ} (h : n ∈ p.derivative.support) :
    n + 1 ∈ p.support :=
  mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
    mem_support_iff.1 h <| show p.derivative.coeff n = 0 by rw [coeff_derivative, h1, zero_mul]
#align polynomial.of_mem_support_derivative Polynomial.of_mem_support_derivative

theorem degree_derivative_lt {p : R[X]} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
  (Finset.sup_lt_iff <| bot_lt_iff_ne_bot.2 <| mt degree_eq_bot.1 hp).2 fun n hp =>
    lt_of_lt_of_le (WithBot.some_lt_some.2 n.lt_succ_self) <|
      Finset.le_sup <| of_mem_support_derivative hp
#align polynomial.degree_derivative_lt Polynomial.degree_derivative_lt

theorem degree_derivative_le {p : R[X]} : p.derivative.degree ≤ p.degree :=
  if H : p = 0 then le_of_eq <| by rw [H, derivative_zero] else (degree_derivative_lt H).le
#align polynomial.degree_derivative_le Polynomial.degree_derivative_le

theorem natDegree_derivative_lt {p : R[X]} (hp : p.natDegree ≠ 0) :
    p.derivative.natDegree < p.natDegree := by
  cases' eq_or_ne (derivative p) 0 with hp' hp'
  · rw [hp', Polynomial.natDegree_zero]
    exact hp.bot_lt
  · rw [natDegree_lt_natDegree_iff hp']
    exact degree_derivative_lt fun h => hp (h.symm ▸ natDegree_zero)
#align polynomial.nat_degree_derivative_lt Polynomial.natDegree_derivative_lt

theorem natDegree_derivative_le (p : R[X]) : p.derivative.natDegree ≤ p.natDegree - 1 := by
  by_cases p0 : p.natDegree = 0
  · simp [p0, derivative_of_natDegree_zero]
  · exact Nat.le_pred_of_lt (natDegree_derivative_lt p0)
#align polynomial.nat_degree_derivative_le Polynomial.natDegree_derivative_le

@[simp]
theorem derivative_nat_cast {n : ℕ} : derivative (n : R[X]) = 0 := by
  rw [← map_natCast C n]
  exact derivative_C
#align polynomial.derivative_nat_cast Polynomial.derivative_nat_cast

--Porting note: new theorem
@[simp]
theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    derivative (no_index (OfNat.ofNat n) : R[X]) = 0 :=
  derivative_nat_cast

theorem iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.natDegree < x) :
    Polynomial.derivative^[x] p = 0 := by
  induction' h : p.natDegree using Nat.strong_induction_on with _ ih generalizing p x
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, iterate_derivative_zero]
  have := natDegree_derivative_lt hp
  exact ih _ this (this.trans_le <| Nat.le_of_lt_succ hx) rfl
#align polynomial.iterate_derivative_eq_zero Polynomial.iterate_derivative_eq_zero

@[simp]
theorem iterate_derivative_C {k} (h : 0 < k) : derivative^[k] (C a : R[X]) = 0 :=
  iterate_derivative_eq_zero <| (natDegree_C _).trans_lt h
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_C Polynomial.iterate_derivative_C

@[simp]
theorem iterate_derivative_one {k} (h : 0 < k) : derivative^[k] (1 : R[X]) = 0 :=
  iterate_derivative_C h
#align polynomial.iterate_derivative_one Polynomial.iterate_derivative_one

@[simp]
theorem iterate_derivative_X {k} (h : 1 < k) : derivative^[k] (X : R[X]) = 0 :=
  iterate_derivative_eq_zero <| natDegree_X_le.trans_lt h
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X Polynomial.iterate_derivative_X

theorem natDegree_eq_zero_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]}
    (h : derivative f = 0) : f.natDegree = 0 := by
  rcases eq_or_ne f 0 with (rfl | hf)
  · exact natDegree_zero
  rw [natDegree_eq_zero_iff_degree_le_zero]
  by_contra' f_nat_degree_pos
  rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
  let m := f.natDegree - 1
  have hm : m + 1 = f.natDegree := tsub_add_cancel_of_le f_nat_degree_pos
  have h2 := coeff_derivative f m
  rw [Polynomial.ext_iff] at h
  rw [h m, coeff_zero, ← Nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2
  replace h2 := h2.resolve_left m.succ_ne_zero
  rw [hm, ← leadingCoeff, leadingCoeff_eq_zero] at h2
  exact hf h2
#align polynomial.nat_degree_eq_zero_of_derivative_eq_zero Polynomial.natDegree_eq_zero_of_derivative_eq_zero

theorem eq_C_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]} (h : derivative f = 0) :
    f = C (f.coeff 0) :=
  eq_C_of_natDegree_eq_zero <| natDegree_eq_zero_of_derivative_eq_zero h
set_option linter.uppercaseLean3 false in
#align polynomial.eq_C_of_derivative_eq_zero Polynomial.eq_C_of_derivative_eq_zero

@[simp]
theorem derivative_mul {f g : R[X]} : derivative (f * g) = derivative f * g + f * derivative g :=
  calc
    derivative (f * g) =
        f.sum fun n a => g.sum fun m b => (n + m) • (C (a * b) * X ^ (n + m - 1)) := by
      rw [mul_eq_sum_sum, derivative_sum]
      trans
      · apply Finset.sum_congr rfl
        intro x _
        exact derivative_sum
      apply Finset.sum_congr rfl; intro n _; apply Finset.sum_congr rfl; intro m _
      trans
      · exact congr_arg _ C_mul_X_pow_eq_monomial.symm
      dsimp; rw [← smul_mul_assoc, smul_C, nsmul_eq_mul']; exact derivative_C_mul_X_pow _ _
    _ =
        f.sum fun n a =>
          g.sum fun m b =>
            n • (C a * X ^ (n - 1)) * (C b * X ^ m) + C a * X ^ n * m • (C b * X ^ (m - 1)) :=
      (sum_congr rfl fun n hn =>
        sum_congr rfl fun m hm => by
          cases n <;> cases m <;>
            simp_rw [add_smul, mul_smul_comm, smul_mul_assoc, X_pow_mul_assoc, ← mul_assoc, ←
              C_mul, mul_assoc, ← pow_add] <;>
            simp [Nat.add_succ, Nat.succ_add, Nat.succ_sub_one, zero_smul, add_comm])
    _ = derivative f * g + f * derivative g := by
      conv =>
        rhs
        congr
        · rw [← sum_C_mul_X_pow_eq g]
        · rw [← sum_C_mul_X_pow_eq f]
      simp only [sum, sum_add_distrib, Finset.mul_sum, Finset.sum_mul, derivative_apply]
      simp_rw [← smul_mul_assoc, smul_C, nsmul_eq_mul']
      rw [Finset.sum_comm]
      congr 1
      rw [Finset.sum_comm]
#align polynomial.derivative_mul Polynomial.derivative_mul

theorem derivative_eval (p : R[X]) (x : R) :
    p.derivative.eval x = p.sum fun n a => a * n * x ^ (n - 1) := by
  simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]
#align polynomial.derivative_eval Polynomial.derivative_eval

@[simp]
theorem derivative_map [Semiring S] (p : R[X]) (f : R →+* S) :
    derivative (p.map f) = p.derivative.map f := by
  let n := max p.natDegree (map f p).natDegree
  rw [derivative_apply, derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, coeff_map,
    map_natCast, Polynomial.map_nat_cast, Polynomial.map_pow, map_X]
  all_goals intro n; rw [zero_mul, C_0, zero_mul]
#align polynomial.derivative_map Polynomial.derivative_map

@[simp]
theorem iterate_derivative_map [Semiring S] (p : R[X]) (f : R →+* S) (k : ℕ) :
    Polynomial.derivative^[k] (p.map f) = (Polynomial.derivative^[k] p).map f := by
  induction' k with k ih generalizing p
  · simp
  · simp only [ih, Function.iterate_succ, Polynomial.derivative_map, Function.comp_apply]
#align polynomial.iterate_derivative_map Polynomial.iterate_derivative_map

theorem derivative_nat_cast_mul {n : ℕ} {f : R[X]} :
    derivative ((n : R[X]) * f) = n * derivative f := by
  simp
#align polynomial.derivative_nat_cast_mul Polynomial.derivative_nat_cast_mul

@[simp]
theorem iterate_derivative_nat_cast_mul {n k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction' k with k ih generalizing f <;> simp [*]
#align polynomial.iterate_derivative_nat_cast_mul Polynomial.iterate_derivative_nat_cast_mul

theorem mem_support_derivative [NoZeroSMulDivisors ℕ R] (p : R[X]) (n : ℕ) :
    n ∈ (derivative p).support ↔ n + 1 ∈ p.support := by
  suffices ¬p.coeff (n + 1) * (n + 1 : ℕ) = 0 ↔ coeff p (n + 1) ≠ 0 by
    simpa only [mem_support_iff, coeff_derivative, Ne.def, Nat.cast_succ]
  rw [← nsmul_eq_mul', smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or_iff]
#align polynomial.mem_support_derivative Polynomial.mem_support_derivative

@[simp]
theorem degree_derivative_eq [NoZeroSMulDivisors ℕ R] (p : R[X]) (hp : 0 < natDegree p) :
    degree (derivative p) = (natDegree p - 1 : ℕ) := by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    simp only [Nat.cast_withBot]
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine' le_sup _
    rw [mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff]
    · show ¬leadingCoeff p = 0
      rw [leadingCoeff_eq_zero]
      intro h
      rw [h, natDegree_zero] at hp
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp)
    exact hp
#align polynomial.degree_derivative_eq Polynomial.degree_derivative_eq

theorem coeff_iterate_derivative_as_prod_Ico {k} (p : R[X]) : ∀ m : ℕ,
    (derivative^[k] p).coeff m = (∏ i in Ico m.succ (m + k.succ), i) • p.coeff (m + k) := by
  induction' k with k ih
  · simp [add_zero, forall_const, one_smul, Ico_self, eq_self_iff_true,
      Function.iterate_zero_apply, prod_empty]
  · intro m
    rw [Function.iterate_succ_apply', coeff_derivative, ih (m + 1), ← Nat.cast_add_one, ←
      nsmul_eq_mul', smul_smul, mul_comm]
    apply congr_arg₂
    · have set_eq : Ico m.succ (m + k.succ.succ) = Ico (m + 1).succ (m + 1 + k.succ) ∪ {m + 1} := by
        simp_rw [← Nat.Ico_succ_singleton, union_comm, Nat.succ_eq_add_one, add_comm (k + 1),
          add_assoc]
        rw [Ico_union_Ico_eq_Ico] <;> simp
      rw [set_eq, prod_union, prod_singleton]
      · rw [disjoint_singleton_right, mem_Ico]
        exact fun h => (Nat.lt_succ_self _).not_le h.1
    · exact congr_arg _ (Nat.succ_add m k)
#align polynomial.coeff_iterate_derivative_as_prod_Ico Polynomial.coeff_iterate_derivative_as_prod_Ico

theorem coeff_iterate_derivative_as_prod_range {k} (p : R[X]) :
    ∀ m : ℕ, (derivative^[k] p).coeff m = (∏ i in range k, (m + k - i)) • p.coeff (m + k) := by
  induction' k with k ih
  · simp
  intro m
  calc
    (derivative^[k + 1] p).coeff m =
        (∏ i in range k, (m + k.succ - i)) • p.coeff (m + k.succ) * (m + 1) :=
      by rw [Function.iterate_succ_apply', coeff_derivative, ih m.succ, Nat.succ_add, Nat.add_succ]
    _ = ((∏ i in range k, (m + k.succ - i)) * (m + 1)) • p.coeff (m + k.succ) := by
      rw [← Nat.cast_add_one, ← nsmul_eq_mul', smul_smul, mul_comm]
    _ = (∏ i in range k.succ, (m + k.succ - i)) • p.coeff (m + k.succ) := by
      rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, Nat.succ_sub le_rfl, tsub_self]
#align polynomial.coeff_iterate_derivative_as_prod_range Polynomial.coeff_iterate_derivative_as_prod_range

theorem iterate_derivative_mul {n} (p q : R[X]) :
    derivative^[n] (p * q) =
      ∑ k in range n.succ, (n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
  induction' n with n IH
  · simp [Finset.range]
  calc
    derivative^[n + 1] (p * q) =
        derivative (∑ k : ℕ in range n.succ,
            n.choose k • (derivative^[n - k] p * derivative^[k] q)) :=
      by rw [Function.iterate_succ_apply', IH]
    _ = (∑ k : ℕ in range n.succ,
          n.choose k • (derivative^[n - k + 1] p * derivative^[k] q)) +
        ∑ k : ℕ in range n.succ,
          n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) := by
      simp_rw [derivative_sum, derivative_smul, derivative_mul, Function.iterate_succ_apply',
        smul_add, sum_add_distrib]
    _ = (∑ k : ℕ in range n.succ,
              n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
            1 • (derivative^[n + 1] p * derivative^[0] q) +
          ∑ k : ℕ in range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) :=
      ?_
    _ = ((∑ k : ℕ in range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q)) +
            ∑ k : ℕ in range n.succ,
              n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
          1 • (derivative^[n + 1] p * derivative^[0] q) :=
      by rw [add_comm, add_assoc]
    _ = (∑ i : ℕ in range n.succ,
            (n + 1).choose (i + 1) • (derivative^[n + 1 - (i + 1)] p * derivative^[i + 1] q)) +
          1 • (derivative^[n + 1] p * derivative^[0] q) :=
      by simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
    _ = ∑ k : ℕ in range n.succ.succ,
          n.succ.choose k • (derivative^[n.succ - k] p * derivative^[k] q) :=
      by rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
  congr
  refine' (sum_range_succ' _ _).trans (congr_arg₂ (· + ·) _ _)
  · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
    refine' sum_congr rfl fun k hk => _
    rw [mem_range] at hk
    congr
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hk), Nat.succ_sub_succ]
  · rw [Nat.choose_zero_right, tsub_zero]
#align polynomial.iterate_derivative_mul Polynomial.iterate_derivative_mul

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem derivative_pow_succ (p : R[X]) (n : ℕ) :
    derivative (p ^ (n + 1)) = C (n + 1 : R) * p ^ n * derivative p :=
  Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ', derivative_mul, ih, Nat.add_one, mul_right_comm, C_add,
      add_mul, add_mul, pow_succ', ← mul_assoc, C_1, one_mul]; simp [add_mul]
#align polynomial.derivative_pow_succ Polynomial.derivative_pow_succ

theorem derivative_pow (p : R[X]) (n : ℕ) :
    derivative (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p :=
  Nat.casesOn n (by rw [pow_zero, derivative_one, Nat.cast_zero, C_0, zero_mul, zero_mul]) fun n =>
    by rw [p.derivative_pow_succ n, n.succ_sub_one, n.cast_succ]
#align polynomial.derivative_pow Polynomial.derivative_pow

theorem derivative_sq (p : R[X]) : derivative (p ^ 2) = C 2 * p * derivative p := by
  rw [derivative_pow_succ, Nat.cast_one, one_add_one_eq_two, pow_one]
#align polynomial.derivative_sq Polynomial.derivative_sq

theorem dvd_iterate_derivative_pow (f : R[X]) (n : ℕ) {m : ℕ} (c : R) (hm : m ≠ 0) :
    (n : R) ∣ eval c (derivative^[m] (f ^ n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply, derivative_pow, mul_assoc, C_eq_nat_cast,
    iterate_derivative_nat_cast_mul, eval_mul, eval_nat_cast]
  exact dvd_mul_right _ _
#align polynomial.dvd_iterate_derivative_pow Polynomial.dvd_iterate_derivative_pow

theorem iterate_derivative_X_pow_eq_nat_cast_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = ↑(Nat.descFactorial n k : R[X]) * X ^ (n - k) := by
  induction' k with k ih
  · erw [Function.iterate_zero_apply, tsub_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul]
  · rw [Function.iterate_succ_apply', ih, derivative_nat_cast_mul, derivative_X_pow, C_eq_nat_cast,
      Nat.succ_eq_add_one, Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul];
    simp [mul_comm, mul_assoc, mul_left_comm]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_pow_eq_nat_cast_mul Polynomial.iterate_derivative_X_pow_eq_nat_cast_mul

theorem iterate_derivative_X_pow_eq_C_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = C (Nat.descFactorial n k : R) * X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_nat_cast_mul n k, C_eq_nat_cast]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_pow_eq_C_mul Polynomial.iterate_derivative_X_pow_eq_C_mul

theorem iterate_derivative_X_pow_eq_smul (n : ℕ) (k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = (Nat.descFactorial n k : R) • X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_C_mul n k, smul_eq_C_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_pow_eq_smul Polynomial.iterate_derivative_X_pow_eq_smul

theorem derivative_X_add_C_pow (c : R) (m : ℕ) :
    derivative ((X + C c) ^ m) = C (m : R) * (X + C c) ^ (m - 1) := by
  rw [derivative_pow, derivative_X_add_C, mul_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_add_C_pow Polynomial.derivative_X_add_C_pow

theorem derivative_X_add_C_sq (c : R) : derivative ((X + C c) ^ 2) = C 2 * (X + C c) := by
  rw [derivative_sq, derivative_X_add_C, mul_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_add_C_sq Polynomial.derivative_X_add_C_sq

theorem iterate_derivative_X_add_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X + C c) ^ n) =
     ((∏ i in Finset.range k, (n - i) : ℕ) : R[X]) * (X + C c) ^ (n - k) := by
  induction' k with k IH
  · simp
  · simp only [Function.iterate_succ_apply', IH, derivative_mul, zero_mul, derivative_nat_cast,
      zero_add, Finset.prod_range_succ, C_eq_nat_cast, Nat.sub_sub, ← mul_assoc,
      derivative_X_add_C_pow, Nat.succ_eq_add_one, Nat.cast_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_add_pow Polynomial.iterate_derivative_X_add_pow

theorem derivative_comp (p q : R[X]) :
    derivative (p.comp q) = derivative q * p.derivative.comp q := by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_nat_cast, zero_add, RingHom.map_mul]
    ring
#align polynomial.derivative_comp Polynomial.derivative_comp

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : R[X]) :
    derivative (p.eval₂ C q) = p.derivative.eval₂ C q * derivative q :=
  Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
    fun n r ih => by
    rw [pow_succ', ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih, @derivative_mul _ _ _ X,
      derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X, add_mul, mul_right_comm]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_eval₂_C Polynomial.derivative_eval₂_C

theorem derivative_prod {s : Multiset ι} {f : ι → R[X]} :
    derivative (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * derivative (f i)) s).sum := by
  refine' Multiset.induction_on s (by simp) fun i s h => _
  rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, Multiset.map_cons _ i s,
    Multiset.sum_cons, Multiset.erase_cons_head, mul_comm (derivative (f i))]
  congr
  rw [h, ← AddMonoidHom.coe_mulLeft, (AddMonoidHom.mulLeft (f i)).map_multiset_sum _,
    AddMonoidHom.coe_mulLeft]
  simp only [Function.comp_apply, Multiset.map_map]
  refine' congr_arg _ (Multiset.map_congr rfl fun j hj => _)
  rw [← mul_assoc, ← Multiset.prod_cons, ← Multiset.map_cons]
  by_cases hij : i = j
  · simp [hij, ← Multiset.prod_cons, ← Multiset.map_cons, Multiset.cons_erase hj]
  · simp [hij]
#align polynomial.derivative_prod Polynomial.derivative_prod

end CommSemiring

section Ring

variable [Ring R]

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_neg (f : R[X]) : derivative (-f) = -derivative f :=
  LinearMap.map_neg derivative f
#align polynomial.derivative_neg Polynomial.derivative_neg

@[simp]
theorem iterate_derivative_neg {f : R[X]} {k : ℕ} : derivative^[k] (-f) = -derivative^[k] f :=
  (@derivative R _).toAddMonoidHom.iterate_map_neg _ _
#align polynomial.iterate_derivative_neg Polynomial.iterate_derivative_neg

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_sub {f g : R[X]} : derivative (f - g) = derivative f - derivative g :=
  LinearMap.map_sub derivative f g
#align polynomial.derivative_sub Polynomial.derivative_sub

--Porting note: removed `simp`: `simp` can prove it.
theorem derivative_X_sub_C (c : R) : derivative (X - C c) = 1 := by
  rw [derivative_sub, derivative_X, derivative_C, sub_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_sub_C Polynomial.derivative_X_sub_C

@[simp]
theorem iterate_derivative_sub {k : ℕ} {f g : R[X]} :
    derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g := by
  induction' k with k ih generalizing f g <;> simp [*]
#align polynomial.iterate_derivative_sub Polynomial.iterate_derivative_sub

@[simp]
theorem derivative_int_cast {n : ℤ} : derivative (n : R[X]) = 0 := by
  rw [← C_eq_int_cast n]
  exact derivative_C
#align polynomial.derivative_int_cast Polynomial.derivative_int_cast

theorem derivative_int_cast_mul {n : ℤ} {f : R[X]} : derivative ((n : R[X]) * f) =
    n * derivative f := by
  simp
#align polynomial.derivative_int_cast_mul Polynomial.derivative_int_cast_mul

@[simp]
theorem iterate_derivative_int_cast_mul {n : ℤ} {k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction' k with k ih generalizing f <;> simp [*]
#align polynomial.iterate_derivative_int_cast_mul Polynomial.iterate_derivative_int_cast_mul

end Ring

section CommRing

variable [CommRing R]

theorem derivative_comp_one_sub_X (p : R[X]) :
    derivative (p.comp (1 - X)) = -p.derivative.comp (1 - X) := by simp [derivative_comp]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_comp_one_sub_X Polynomial.derivative_comp_one_sub_X

@[simp]
theorem iterate_derivative_comp_one_sub_X (p : R[X]) (k : ℕ) :
    derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (derivative^[k] p).comp (1 - X) := by
  induction' k with k ih generalizing p
  · simp
  · simp [ih (derivative p), iterate_derivative_neg, derivative_comp, pow_succ]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_comp_one_sub_X Polynomial.iterate_derivative_comp_one_sub_X

theorem eval_multiset_prod_X_sub_C_derivative {S : Multiset R} {r : R} (hr : r ∈ S) :
    eval r (derivative (Multiset.map (fun a => X - C a) S).prod) =
      (Multiset.map (fun a => r - a) (S.erase r)).prod := by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))
  simpa using this
set_option linter.uppercaseLean3 false in
#align polynomial.eval_multiset_prod_X_sub_C_derivative Polynomial.eval_multiset_prod_X_sub_C_derivative

theorem derivative_X_sub_C_pow (c : R) (m : ℕ) :
    derivative ((X - C c) ^ m) = C (m : R) * (X - C c) ^ (m - 1) := by
  rw [derivative_pow, derivative_X_sub_C, mul_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_sub_C_pow Polynomial.derivative_X_sub_C_pow

theorem derivative_X_sub_C_sq (c : R) : derivative ((X - C c) ^ 2) = C 2 * (X - C c) := by
  rw [derivative_sq, derivative_X_sub_C, mul_one]
set_option linter.uppercaseLean3 false in
#align polynomial.derivative_X_sub_C_sq Polynomial.derivative_X_sub_C_sq

theorem iterate_derivative_X_sub_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X - C c) ^ n) = ((∏ i in Finset.range k, (n - i) : ℕ) : R[X]) *
    (X - C c) ^ (n - k) := by
  rw [sub_eq_add_neg, ← C_neg, iterate_derivative_X_add_pow]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_sub_pow Polynomial.iterate_derivative_X_sub_pow

end CommRing

end Derivative

end Polynomial
