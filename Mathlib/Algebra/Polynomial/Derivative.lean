/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# The derivative map on polynomials

## Main definitions
* `Polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.
* `Polynomial.derivativeFinsupp`: Iterated derivatives as a finite support function.

-/


noncomputable section

open Finset

open Polynomial

open scoped Nat

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
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, RingHom.map_add, zero_mul, RingHom.map_zero]
  map_smul' a p := by
    dsimp; rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, RingHom.map_mul, forall_const, zero_mul,
        RingHom.map_zero, sum]

theorem derivative_apply (p : R[X]) : derivative p = p.sum fun n a => C (a * n) * X ^ (n - 1) :=
  rfl

theorem coeff_derivative (p : R[X]) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (n + 1) := by
  rw [derivative_apply]
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
  rw [sum, Finset.sum_eq_single (n + 1)]
  · simp only [Nat.add_succ_sub_one, add_zero, mul_one, if_true]; norm_cast
  · intro b
    cases b
    · intros
      rw [Nat.cast_zero, mul_zero, zero_mul]
    · intro _ H
      rw [Nat.add_one_sub_one, if_neg (mt (congr_arg Nat.succ) H.symm), mul_zero]
  · simp_all

@[simp]
theorem derivative_zero : derivative (0 : R[X]) = 0 :=
  derivative.map_zero

theorem iterate_derivative_zero {k : ℕ} : derivative^[k] (0 : R[X]) = 0 :=
  iterate_map_zero derivative k

theorem derivative_monomial (a : R) (n : ℕ) :
    derivative (monomial n a) = monomial (n - 1) (a * n) := by
  rw [derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial]
  simp

@[simp]
theorem derivative_monomial_succ (a : R) (n : ℕ) :
    derivative (monomial (n + 1) a) = monomial n (a * (n + 1)) := by
  rw [derivative_monomial, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]

theorem derivative_C_mul_X (a : R) : derivative (C a * X) = C a := by
  simp [C_mul_X_eq_monomial, mul_one]

theorem derivative_C_mul_X_pow (a : R) (n : ℕ) :
    derivative (C a * X ^ n) = C (a * n) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]

theorem derivative_C_mul_X_sq (a : R) : derivative (C a * X ^ 2) = C (a * 2) * X := by
  rw [derivative_C_mul_X_pow, Nat.cast_two, pow_one]

theorem derivative_X_pow (n : ℕ) : derivative (X ^ n : R[X]) = C (n : R) * X ^ (n - 1) := by
  convert derivative_C_mul_X_pow (1 : R) n <;> simp

@[simp]
theorem derivative_X_pow_succ (n : ℕ) :
    derivative (X ^ (n + 1) : R[X]) = C (n + 1 : R) * X ^ n := by
  simp [derivative_X_pow]

theorem derivative_X_sq : derivative (X ^ 2 : R[X]) = C 2 * X := by
  rw [derivative_X_pow, Nat.cast_two, pow_one]

@[simp]
theorem derivative_C {a : R} : derivative (C a) = 0 := by simp [derivative_apply]

theorem derivative_of_natDegree_zero {p : R[X]} (hp : p.natDegree = 0) : derivative p = 0 := by
  rw [eq_C_of_natDegree_eq_zero hp, derivative_C]

@[simp]
theorem derivative_X : derivative (X : R[X]) = 1 :=
  (derivative_monomial _ _).trans <| by simp

@[simp]
theorem derivative_one : derivative (1 : R[X]) = 0 :=
  derivative_C

@[simp]
theorem derivative_add {f g : R[X]} : derivative (f + g) = derivative f + derivative g :=
  derivative.map_add f g

theorem derivative_X_add_C (c : R) : derivative (X + C c) = 1 := by
  rw [derivative_add, derivative_X, derivative_C, add_zero]

theorem derivative_sum {s : Finset ι} {f : ι → R[X]} :
    derivative (∑ b ∈ s, f b) = ∑ b ∈ s, derivative (f b) :=
  map_sum ..

theorem iterate_derivative_sum (k : ℕ) (s : Finset ι) (f : ι → R[X]) :
    derivative^[k] (∑ b ∈ s, f b) = ∑ b ∈ s, derivative^[k] (f b) := by
  simp_rw [← Module.End.pow_apply, map_sum]

theorem derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] (s : S)
    (p : R[X]) : derivative (s • p) = s • derivative p :=
  derivative.map_smul_of_tower s p

@[simp]
theorem iterate_derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R]
    (s : S) (p : R[X]) (k : ℕ) : derivative^[k] (s • p) = s • derivative^[k] p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih]

@[simp]
theorem iterate_derivative_C_mul (a : R) (p : R[X]) (k : ℕ) :
    derivative^[k] (C a * p) = C a * derivative^[k] p := by
  simp_rw [← smul_eq_C_mul, iterate_derivative_smul]

theorem derivative_C_mul (a : R) (p : R[X]) :
    derivative (C a * p) = C a * derivative p := iterate_derivative_C_mul _ _ 1

theorem of_mem_support_derivative {p : R[X]} {n : ℕ} (h : n ∈ p.derivative.support) :
    n + 1 ∈ p.support :=
  mem_support_iff.2 fun h1 : p.coeff (n + 1) = 0 =>
    mem_support_iff.1 h <| show p.derivative.coeff n = 0 by rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : R[X]} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
  (Finset.sup_lt_iff <| bot_lt_iff_ne_bot.2 <| mt degree_eq_bot.1 hp).2 fun n hp =>
    lt_of_lt_of_le (WithBot.coe_lt_coe.2 n.lt_succ_self) <|
      Finset.le_sup <| of_mem_support_derivative hp

theorem degree_derivative_le {p : R[X]} : p.derivative.degree ≤ p.degree :=
  letI := Classical.decEq R
  if H : p = 0 then le_of_eq <| by rw [H, derivative_zero] else (degree_derivative_lt H).le

theorem natDegree_derivative_lt {p : R[X]} (hp : p.natDegree ≠ 0) :
    p.derivative.natDegree < p.natDegree := by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [hp', Polynomial.natDegree_zero]
    exact hp.bot_lt
  · rw [natDegree_lt_natDegree_iff hp']
    exact degree_derivative_lt fun h => hp (h.symm ▸ natDegree_zero)

theorem natDegree_derivative_le (p : R[X]) : p.derivative.natDegree ≤ p.natDegree - 1 := by
  by_cases p0 : p.natDegree = 0
  · simp [p0, derivative_of_natDegree_zero]
  · exact Nat.le_sub_one_of_lt (natDegree_derivative_lt p0)

theorem natDegree_iterate_derivative (p : R[X]) (k : ℕ) :
    (derivative^[k] p).natDegree ≤ p.natDegree - k := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.sub_zero]
  | succ d hd =>
      rw [Function.iterate_succ_apply', Nat.sub_succ']
      exact (natDegree_derivative_le _).trans <| Nat.sub_le_sub_right hd 1

@[simp]
theorem derivative_natCast {n : ℕ} : derivative (n : R[X]) = 0 := by
  rw [← map_natCast C n]
  exact derivative_C

@[simp]
theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    derivative (ofNat(n) : R[X]) = 0 :=
  derivative_natCast

theorem iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.natDegree < x) :
    Polynomial.derivative^[x] p = 0 := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with | _ _ ih
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hp, iterate_derivative_zero]
  have := natDegree_derivative_lt hp
  exact ih _ this (this.trans_le <| Nat.le_of_lt_succ hx) rfl

@[simp]
theorem iterate_derivative_C {k} (h : 0 < k) : derivative^[k] (C a : R[X]) = 0 :=
  iterate_derivative_eq_zero <| (natDegree_C _).trans_lt h

@[simp]
theorem iterate_derivative_one {k} (h : 0 < k) : derivative^[k] (1 : R[X]) = 0 :=
  iterate_derivative_C h

@[simp]
theorem iterate_derivative_X {k} (h : 1 < k) : derivative^[k] (X : R[X]) = 0 :=
  iterate_derivative_eq_zero <| natDegree_X_le.trans_lt h

theorem natDegree_eq_zero_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]}
    (h : derivative f = 0) : f.natDegree = 0 := by
  rcases eq_or_ne f 0 with (rfl | hf)
  · exact natDegree_zero
  rw [natDegree_eq_zero_iff_degree_le_zero]
  by_contra! f_nat_degree_pos
  rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
  let m := f.natDegree - 1
  have hm : m + 1 = f.natDegree := tsub_add_cancel_of_le f_nat_degree_pos
  have h2 := coeff_derivative f m
  rw [Polynomial.ext_iff] at h
  rw [h m, coeff_zero, ← Nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2
  replace h2 := h2.resolve_left m.succ_ne_zero
  rw [hm, ← leadingCoeff, leadingCoeff_eq_zero] at h2
  exact hf h2

theorem eq_C_of_derivative_eq_zero [NoZeroSMulDivisors ℕ R] {f : R[X]} (h : derivative f = 0) :
    f = C (f.coeff 0) :=
  eq_C_of_natDegree_eq_zero <| natDegree_eq_zero_of_derivative_eq_zero h

@[simp]
theorem derivative_mul {f g : R[X]} : derivative (f * g) = derivative f * g + f * derivative g := by
  induction f using Polynomial.induction_on' with
  | add => simp only [add_mul, map_add, add_assoc, add_left_comm, *]
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add => simp only [mul_add, map_add, add_assoc, add_left_comm, *]
  | monomial n b => ?_
  simp only [monomial_mul_monomial, derivative_monomial]
  simp only [mul_assoc, (Nat.cast_commute _ _).eq, Nat.cast_add, mul_add, map_add]
  cases m with
  | zero => simp only [zero_add, Nat.cast_zero, mul_zero, map_zero]
  | succ m =>
  cases n with
  | zero => simp only [add_zero, Nat.cast_zero, mul_zero, map_zero]
  | succ n =>
  simp only [Nat.add_succ_sub_one, add_tsub_cancel_right]
  rw [add_assoc, add_comm n 1]

theorem derivative_eval (p : R[X]) (x : R) :
    p.derivative.eval x = p.sum fun n a => a * n * x ^ (n - 1) := by
  simp_rw [derivative_apply, eval_sum, eval_mul_X_pow, eval_C]

@[simp]
theorem derivative_map [Semiring S] (p : R[X]) (f : R →+* S) :
    derivative (p.map f) = p.derivative.map f := by
  let n := max p.natDegree (map f p).natDegree
  rw [derivative_apply, derivative_apply]
  rw [sum_over_range' _ _ (n + 1) ((le_max_left _ _).trans_lt (lt_add_one _))]
  on_goal 1 => rw [sum_over_range' _ _ (n + 1) ((le_max_right _ _).trans_lt (lt_add_one _))]
  · simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, coeff_map,
      map_natCast, Polynomial.map_natCast, Polynomial.map_pow, map_X]
  all_goals intro n; rw [zero_mul, C_0, zero_mul]

@[simp]
theorem iterate_derivative_map [Semiring S] (p : R[X]) (f : R →+* S) (k : ℕ) :
    Polynomial.derivative^[k] (p.map f) = (Polynomial.derivative^[k] p).map f := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    simp only [ih, Function.iterate_succ, Polynomial.derivative_map, Function.comp_apply]

theorem derivative_natCast_mul {n : ℕ} {f : R[X]} :
    derivative ((n : R[X]) * f) = n * derivative f := by
  simp

@[simp]
theorem iterate_derivative_natCast_mul {n k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction k generalizing f <;> simp [*]

theorem mem_support_derivative [NoZeroSMulDivisors ℕ R] (p : R[X]) (n : ℕ) :
    n ∈ (derivative p).support ↔ n + 1 ∈ p.support := by
  suffices ¬p.coeff (n + 1) * (n + 1 : ℕ) = 0 ↔ coeff p (n + 1) ≠ 0 by
    simpa only [mem_support_iff, coeff_derivative, Ne, Nat.cast_succ]
  rw [← nsmul_eq_mul', smul_eq_zero]
  simp only [Nat.succ_ne_zero, false_or]

@[simp]
theorem degree_derivative_eq [NoZeroSMulDivisors ℕ R] (p : R[X]) (hp : 0 < natDegree p) :
    degree (derivative p) = (natDegree p - 1 : ℕ) := by
  apply le_antisymm
  · rw [derivative_apply]
    apply le_trans (degree_sum_le _ _) (Finset.sup_le _)
    intro n hn
    apply le_trans (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
    apply le_natDegree_of_mem_supp _ hn
  · refine le_sup ?_
    rw [mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff]
    · rw [coeff_natDegree, Ne, leadingCoeff_eq_zero]
      intro h
      rw [h, natDegree_zero] at hp
      exact hp.false
    exact hp

theorem coeff_iterate_derivative {k} (p : R[X]) (m : ℕ) :
    (derivative^[k] p).coeff m = (m + k).descFactorial k • p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply', coeff_derivative, ih m.succ, Nat.succ_add, Nat.add_succ]
        _ = ((m + 1) * Nat.descFactorial (Nat.succ (m + k)) k) • p.coeff (m + k.succ) := by
          rw [← Nat.cast_add_one, ← nsmul_eq_mul', smul_smul]
        _ = Nat.descFactorial (m.succ + k) k.succ • p.coeff (m + k.succ) := by
          rw [← Nat.succ_add, Nat.descFactorial_succ, add_tsub_cancel_right]
        _ = Nat.descFactorial (m + k.succ) k.succ • p.coeff (m + k.succ) := by
          rw [Nat.succ_add_eq_add_succ]

theorem iterate_derivative_eq_sum (p : R[X]) (k : ℕ) :
    derivative^[k] p =
      ∑ x ∈ (derivative^[k] p).support, C ((x + k).descFactorial k • p.coeff (x + k)) * X ^ x := by
  conv_lhs => rw [(derivative^[k] p).as_sum_support_C_mul_X_pow]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [coeff_iterate_derivative, Nat.descFactorial_eq_factorial_mul_choose]

theorem iterate_derivative_eq_factorial_smul_sum (p : R[X]) (k : ℕ) :
    derivative^[k] p = k ! •
      ∑ x ∈ (derivative^[k] p).support, C ((x + k).choose k • p.coeff (x + k)) * X ^ x := by
  conv_lhs => rw [iterate_derivative_eq_sum]
  rw [smul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← smul_mul_assoc, smul_C, smul_smul, Nat.descFactorial_eq_factorial_mul_choose]

theorem iterate_derivative_mul {n} (p q : R[X]) :
    derivative^[n] (p * q) =
      ∑ k ∈ range n.succ, (n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
  induction n with
  | zero =>
    simp [Finset.range]
  | succ n IH =>
    calc
      derivative^[n + 1] (p * q) =
          derivative (∑ k ∈ range n.succ,
              n.choose k • (derivative^[n - k] p * derivative^[k] q)) := by
        rw [Function.iterate_succ_apply', IH]
      _ = (∑ k ∈ range n.succ,
            n.choose k • (derivative^[n - k + 1] p * derivative^[k] q)) +
          ∑ k ∈ range n.succ,
            n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) := by
        simp_rw [derivative_sum, derivative_smul, derivative_mul, Function.iterate_succ_apply',
          smul_add, sum_add_distrib]
      _ = (∑ k ∈ range n.succ,
                n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
              1 • (derivative^[n + 1] p * derivative^[0] q) +
            ∑ k ∈ range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q) :=
        ?_
      _ = ((∑ k ∈ range n.succ, n.choose k • (derivative^[n - k] p * derivative^[k + 1] q)) +
              ∑ k ∈ range n.succ,
                n.choose k.succ • (derivative^[n - k] p * derivative^[k + 1] q)) +
            1 • (derivative^[n + 1] p * derivative^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ i ∈ range n.succ,
              (n + 1).choose (i + 1) • (derivative^[n + 1 - (i + 1)] p * derivative^[i + 1] q)) +
            1 • (derivative^[n + 1] p * derivative^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range n.succ.succ,
            n.succ.choose k • (derivative^[n.succ - k] p * derivative^[k] q) := by
        rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      omega
    · rw [Nat.choose_zero_right, tsub_zero]

/--
Iterated derivatives as a finite support function.
-/
@[simps! apply_toFun]
noncomputable def derivativeFinsupp : R[X] →ₗ[R] ℕ →₀ R[X] where
  toFun p := .onFinset (range (p.natDegree + 1)) (derivative^[·] p) fun i ↦ by
    contrapose; simp_all [iterate_derivative_eq_zero, Nat.succ_le]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem support_derivativeFinsupp_subset_range {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    (derivativeFinsupp p).support ⊆ range n := by
  dsimp [derivativeFinsupp]
  exact Finsupp.support_onFinset_subset.trans (Finset.range_subset_range.mpr h)

@[simp]
theorem derivativeFinsupp_C (r : R) : derivativeFinsupp (C r : R[X]) = .single 0 (C r) := by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

@[simp]
theorem derivativeFinsupp_one : derivativeFinsupp (1 : R[X]) = .single 0 1 := by
  simpa using derivativeFinsupp_C (1 : R)

@[simp]
theorem derivativeFinsupp_X : derivativeFinsupp (X : R[X]) = .single 0 X + .single 1 1 := by
  ext i : 1
  match i with
  | 0 => simp
  | 1 => simp
  | (n + 2) => simp

theorem derivativeFinsupp_map [Semiring S] (p : R[X]) (f : R →+* S) :
    derivativeFinsupp (p.map f) = (derivativeFinsupp p).mapRange (·.map f) (by simp) := by
  ext i : 1
  simp

theorem derivativeFinsupp_derivative (p : R[X]) :
    derivativeFinsupp (derivative p) =
      (derivativeFinsupp p).comapDomain Nat.succ Nat.succ_injective.injOn := by
  ext i : 1
  simp

end Semiring

section CommSemiring

variable [CommSemiring R]

theorem derivative_pow_succ (p : R[X]) (n : ℕ) :
    derivative (p ^ (n + 1)) = C (n + 1 : R) * p ^ n * derivative p :=
  Nat.recOn n (by simp) fun n ih => by
    rw [pow_succ, derivative_mul, ih, Nat.add_one, mul_right_comm, C_add,
      add_mul, add_mul, pow_succ, ← mul_assoc, C_1, one_mul]; simp [add_mul]

theorem derivative_pow (p : R[X]) (n : ℕ) :
    derivative (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p :=
  Nat.casesOn n (by rw [pow_zero, derivative_one, Nat.cast_zero, C_0, zero_mul, zero_mul]) fun n =>
    by rw [p.derivative_pow_succ n, Nat.add_one_sub_one, n.cast_succ]

theorem derivative_sq (p : R[X]) : derivative (p ^ 2) = C 2 * p * derivative p := by
  rw [derivative_pow_succ, Nat.cast_one, one_add_one_eq_two, pow_one]

theorem pow_sub_one_dvd_derivative_of_pow_dvd {p q : R[X]} {n : ℕ}
    (dvd : q ^ n ∣ p) : q ^ (n - 1) ∣ derivative p := by
  obtain ⟨r, rfl⟩ := dvd
  rw [derivative_mul, derivative_pow]
  exact (((dvd_mul_left _ _).mul_right _).mul_right _).add ((pow_dvd_pow q n.pred_le).mul_right _)

theorem pow_sub_dvd_iterate_derivative_of_pow_dvd {p q : R[X]} {n : ℕ} (m : ℕ)
    (dvd : q ^ n ∣ p) : q ^ (n - m) ∣ derivative^[m] p := by
  induction m generalizing p with
  | zero => simpa
  | succ m ih =>
    rw [Nat.sub_succ, Function.iterate_succ']
    exact pow_sub_one_dvd_derivative_of_pow_dvd (ih dvd)

theorem pow_sub_dvd_iterate_derivative_pow (p : R[X]) (n m : ℕ) :
    p ^ (n - m) ∣ derivative^[m] (p ^ n) := pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

theorem dvd_iterate_derivative_pow (f : R[X]) (n : ℕ) {m : ℕ} (c : R) (hm : m ≠ 0) :
    (n : R) ∣ eval c (derivative^[m] (f ^ n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [Function.iterate_succ_apply, derivative_pow, mul_assoc, C_eq_natCast,
    iterate_derivative_natCast_mul, eval_mul, eval_natCast]
  exact dvd_mul_right _ _

theorem iterate_derivative_X_pow_eq_natCast_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = ↑(Nat.descFactorial n k : R[X]) * X ^ (n - k) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, tsub_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_natCast_mul, derivative_X_pow, C_eq_natCast,
      Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul]
    simp [mul_assoc, mul_left_comm]

theorem iterate_derivative_X_pow_eq_C_mul (n k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = C (Nat.descFactorial n k : R) * X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_natCast_mul n k, C_eq_natCast]

theorem iterate_derivative_X_pow_eq_smul (n : ℕ) (k : ℕ) :
    derivative^[k] (X ^ n : R[X]) = (Nat.descFactorial n k : R) • X ^ (n - k) := by
  rw [iterate_derivative_X_pow_eq_C_mul n k, smul_eq_C_mul]

theorem derivative_X_add_C_pow (c : R) (m : ℕ) :
    derivative ((X + C c) ^ m) = C (m : R) * (X + C c) ^ (m - 1) := by
  rw [derivative_pow, derivative_X_add_C, mul_one]

theorem derivative_X_add_C_sq (c : R) : derivative ((X + C c) ^ 2) = C 2 * (X + C c) := by
  rw [derivative_sq, derivative_X_add_C, mul_one]

theorem iterate_derivative_X_add_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X + C c) ^ n) = Nat.descFactorial n k • (X + C c) ^ (n - k) := by
  induction k with
  | zero => simp
  | succ k IH =>
      rw [Nat.sub_succ', Function.iterate_succ_apply', IH, derivative_smul,
        derivative_X_add_C_pow, map_natCast, Nat.descFactorial_succ, nsmul_eq_mul, nsmul_eq_mul,
        Nat.cast_mul]
      ring

theorem derivative_comp (p q : R[X]) :
    derivative (p.comp q) = derivative q * p.derivative.comp q := by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C,
      zero_mul, C_eq_natCast, zero_add, RingHom.map_mul]
    ring

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : R[X]) :
    derivative (p.eval₂ C q) = p.derivative.eval₂ C q * derivative q :=
  Polynomial.induction_on p (fun r => by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ => by
      rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
    fun n r ih => by
    rw [pow_succ, ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih, @derivative_mul _ _ _ X,
      derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X, add_mul, mul_right_comm]

theorem derivative_prod [DecidableEq ι] {s : Multiset ι} {f : ι → R[X]} :
    derivative (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * derivative (f i)) s).sum := by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, Multiset.map_cons _ i s,
    Multiset.sum_cons, Multiset.erase_cons_head, mul_comm (derivative (f i))]
  congr
  rw [h, ← AddMonoidHom.coe_mulLeft, (AddMonoidHom.mulLeft (f i)).map_multiset_sum _,
    AddMonoidHom.coe_mulLeft]
  simp only [Function.comp_apply, Multiset.map_map]
  refine congr_arg _ (Multiset.map_congr rfl fun j hj => ?_)
  rw [← mul_assoc, ← Multiset.prod_cons, ← Multiset.map_cons]
  by_cases hij : i = j
  · simp [hij, Multiset.cons_erase hj]
  · simp [hij]

end CommSemiring

section Ring

variable [Ring R]

@[simp]
theorem derivative_neg (f : R[X]) : derivative (-f) = -derivative f :=
  LinearMap.map_neg derivative f

theorem iterate_derivative_neg {f : R[X]} {k : ℕ} : derivative^[k] (-f) = -derivative^[k] f :=
  iterate_map_neg derivative k f

@[simp]
theorem derivative_sub {f g : R[X]} : derivative (f - g) = derivative f - derivative g :=
  LinearMap.map_sub derivative f g

theorem derivative_X_sub_C (c : R) : derivative (X - C c) = 1 := by
  rw [derivative_sub, derivative_X, derivative_C, sub_zero]

theorem iterate_derivative_sub {k : ℕ} {f g : R[X]} :
    derivative^[k] (f - g) = derivative^[k] f - derivative^[k] g :=
  iterate_map_sub derivative k f g

@[simp]
theorem derivative_intCast {n : ℤ} : derivative (n : R[X]) = 0 := by
  rw [← C_eq_intCast n]
  exact derivative_C

theorem derivative_intCast_mul {n : ℤ} {f : R[X]} : derivative ((n : R[X]) * f) =
    n * derivative f := by
  simp

@[simp]
theorem iterate_derivative_intCast_mul {n : ℤ} {k : ℕ} {f : R[X]} :
    derivative^[k] ((n : R[X]) * f) = n * derivative^[k] f := by
  induction k generalizing f <;> simp [*]

end Ring

section CommRing

variable [CommRing R]

theorem derivative_comp_one_sub_X (p : R[X]) :
    derivative (p.comp (1 - X)) = -p.derivative.comp (1 - X) := by simp [derivative_comp]

@[simp]
theorem iterate_derivative_comp_one_sub_X (p : R[X]) (k : ℕ) :
    derivative^[k] (p.comp (1 - X)) = (-1) ^ k * (derivative^[k] p).comp (1 - X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

theorem eval_multiset_prod_X_sub_C_derivative [DecidableEq R]
    {S : Multiset R} {r : R} (hr : r ∈ S) :
    eval r (derivative (Multiset.map (fun a => X - C a) S).prod) =
      (Multiset.map (fun a => r - a) (S.erase r)).prod := by
  nth_rw 1 [← Multiset.cons_erase hr]
  have := (evalRingHom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))
  simpa using this

theorem derivative_X_sub_C_pow (c : R) (m : ℕ) :
    derivative ((X - C c) ^ m) = C (m : R) * (X - C c) ^ (m - 1) := by
  rw [derivative_pow, derivative_X_sub_C, mul_one]

theorem derivative_X_sub_C_sq (c : R) : derivative ((X - C c) ^ 2) = C 2 * (X - C c) := by
  rw [derivative_sq, derivative_X_sub_C, mul_one]

theorem iterate_derivative_X_sub_pow (n k : ℕ) (c : R) :
    derivative^[k] ((X - C c) ^ n) = n.descFactorial k • (X - C c) ^ (n - k) := by
  rw [sub_eq_add_neg, ← C_neg, iterate_derivative_X_add_pow]

theorem iterate_derivative_X_sub_pow_self (n : ℕ) (c : R) :
    derivative^[n] ((X - C c) ^ n) = n.factorial := by
  rw [iterate_derivative_X_sub_pow, n.sub_self, pow_zero, nsmul_one, n.descFactorial_self]

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

@[simp]
theorem dvd_derivative_iff {P : R[X]} : P ∣ derivative P ↔ derivative P = 0 where
  mp h := by
    by_cases hP : P = 0
    · simp only [hP, derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (degree_derivative_lt hP)
  mpr h := by simp [h]

end NoZeroDivisors

section CommSemiringNoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R]

theorem derivative_pow_eq_zero {n : ℕ} (chn : (n : R) ≠ 0) {a : R[X]} :
    derivative (a ^ n) = 0 ↔ derivative a = 0 := by
  nontriviality R
  rw [← C_ne_zero, C_eq_natCast] at chn
  simp +contextual [derivative_pow, chn]

end CommSemiringNoZeroDivisors

end Derivative

end Polynomial
