/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao

! This file was ported from Lean 3 source module main
-/
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.SpecialFunctions.Polynomials
import Mathbin.Data.Complex.Exponential
import Mathbin.FieldTheory.PolynomialGaloisGroup
import Mathbin.MeasureTheory.Integral.IntervalIntegral
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.RingTheory.Algebraic
import Mathbin.Algebra.CharP.Algebra

-- import gal_conj
-- import gal_conj
-- import symmetric
-- import symmetric
noncomputable section

open scoped BigOperators Classical Polynomial

open Finset

namespace Nat

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i in range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [desc_factorial, prod_range_succ, mul_comm, desc_factorial_eq_prod_range k]
#align nat.desc_factorial_eq_prod_range Nat.descFactorial_eq_prod_range

end Nat

namespace Finsupp

variable {α M N : Type _}

theorem indicator_const_eq_sum_single [AddCommMonoid M] (s : Finset α) (m : M) :
    (indicator s fun _ _ => m) = ∑ x in s, single x m :=
  (indicator_eq_sum_single _ _).trans <| @sum_attach _ _ _ _ fun i => single i m
#align finsupp.indicator_const_eq_sum_single Finsupp.indicator_const_eq_sum_single

@[simp, to_additive]
theorem prod_indicator_const_index [Zero M] [CommMonoid N] {s : Finset α} (m : M) {h : α → M → N}
    (h_zero : ∀ a ∈ s, h a 0 = 1) : (indicator s fun _ _ => m).Prod h = ∏ x in s, h x m :=
  (prod_indicator_index _ h_zero).trans <| @prod_attach _ _ _ _ fun i => h i m
#align finsupp.prod_indicator_const_index Finsupp.prod_indicator_const_index
#align finsupp.sum_indicator_const_index Finsupp.sum_indicator_const_index

end Finsupp

namespace Polynomial

section

variable {R k : Type _} [Semiring R]

theorem mem_roots_map_of_injective {p : R[X]} [CommRing k] [IsDomain k] {f : R →+* k}
    (hf : Function.Injective f) {x : k} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 :=
  by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp)]
  dsimp only [is_root]
  rw [Polynomial.eval_map]
#align polynomial.mem_roots_map_of_injective Polynomial.mem_roots_map_of_injective

end

section

variable {R k : Type _} [CommRing R]

theorem mem_rootSet_of_injective {p : R[X]} [CommRing k] [IsDomain k] [Algebra R k]
    (h : Function.Injective (algebraMap R k)) {x : k} (hp : p ≠ 0) :
    x ∈ p.rootSet k ↔ aeval x p = 0 :=
  Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)
#align polynomial.mem_root_set_of_injective Polynomial.mem_rootSet_of_injective

end

variable {R : Type _}

section Semiring

variable {S : Type _} [Semiring R]

theorem sum_ideriv_apply_of_lt' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    ∑ i in range (p.natDegree + 1), (derivative^[i]) p = ∑ i in range n, (derivative^[i]) p :=
  by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn; rw [hm, add_right_comm]
  rw [sum_range_add _ _ m]; convert (add_zero _).symm; apply sum_eq_zero
  intro x hx; rw [add_comm, Function.iterate_add_apply]
  convert iterate_derivative_zero; rw [iterate_derivative_eq_zero]; exact lt_add_one _
#align polynomial.sum_ideriv_apply_of_lt' Polynomial.sum_ideriv_apply_of_lt'

theorem sum_ideriv_apply_of_le' {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    ∑ i in range (p.natDegree + 1), (derivative^[i]) p = ∑ i in range (n + 1), (derivative^[i]) p :=
  sum_ideriv_apply_of_lt' (Nat.lt_add_one_iff.mpr hn)
#align polynomial.sum_ideriv_apply_of_le' Polynomial.sum_ideriv_apply_of_le'

def sumIderiv : R[X] →ₗ[R] R[X]
    where
  toFun p := ∑ i in range (p.natDegree + 1), (derivative^[i]) p
  map_add' p q :=
    by
    let x := max ((p + q).natDegree + 1) (max (p.nat_degree + 1) (q.nat_degree + 1))
    have hpq : (p + q).natDegree + 1 ≤ x := le_max_left _ _
    have hp : p.nat_degree + 1 ≤ x := (le_max_left _ _).trans (le_max_right _ _)
    have hq : q.nat_degree + 1 ≤ x := (le_max_right _ _).trans (le_max_right _ _)
    simp_rw [sum_ideriv_apply_of_lt' hpq, sum_ideriv_apply_of_lt' hp, sum_ideriv_apply_of_lt' hq, ←
      sum_add_distrib, iterate_derivative_add]
  map_smul' a p := by
    dsimp <;>
      simp_rw [sum_ideriv_apply_of_le' (nat_degree_smul_le _ _), iterate_derivative_smul, smul_sum]
#align polynomial.sum_ideriv Polynomial.sumIderiv

theorem sumIderiv_apply (p : R[X]) :
    p.sumIderiv = ∑ i in range (p.natDegree + 1), (derivative^[i]) p :=
  rfl
#align polynomial.sum_ideriv_apply Polynomial.sumIderiv_apply

theorem sumIderiv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    p.sumIderiv = ∑ i in range n, (derivative^[i]) p :=
  sum_ideriv_apply_of_lt' hn
#align polynomial.sum_ideriv_apply_of_lt Polynomial.sumIderiv_apply_of_lt

theorem sumIderiv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    p.sumIderiv = ∑ i in range (n + 1), (derivative^[i]) p :=
  sum_ideriv_apply_of_le' hn
#align polynomial.sum_ideriv_apply_of_le Polynomial.sumIderiv_apply_of_le

theorem sumIderiv_c (a : R) : (C a).sumIderiv = C a := by
  rw [sum_ideriv_apply, nat_degree_C, zero_add, sum_range_one, Function.iterate_zero_apply]
#align polynomial.sum_ideriv_C Polynomial.sumIderiv_c

@[simp]
theorem sumIderiv_map {S : Type _} [CommSemiring S] (p : R[X]) (f : R →+* S) :
    (p.map f).sumIderiv = p.sumIderiv.map f :=
  by
  let n := max (p.map f).natDegree p.nat_degree
  rw [sum_ideriv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [sum_ideriv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum]
  apply sum_congr rfl; intro x hx
  rw [iterate_derivative_map p f x]
#align polynomial.sum_ideriv_map Polynomial.sumIderiv_map

theorem sumIderiv_derivative (p : R[X]) : p.derivative.sumIderiv = p.sumIderiv.derivative :=
  by
  rw [sum_ideriv_apply_of_le ((nat_degree_derivative_le p).trans tsub_le_self), sum_ideriv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
#align polynomial.sum_ideriv_derivative Polynomial.sumIderiv_derivative

theorem sumIderiv_eq_self_add (p : R[X]) : p.sumIderiv = p + p.derivative.sumIderiv :=
  by
  rw [sum_ideriv_derivative, sum_ideriv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative]; congr
  rw [iterate_derivative_eq_zero (Nat.lt_succ_self _)]
#align polynomial.sum_ideriv_eq_self_add Polynomial.sumIderiv_eq_self_add

def iterateDerivativeLinearMap (n : ℕ) : R[X] →ₗ[R] R[X]
    where
  toFun p := (derivative^[n]) p
  map_add' p q := iterate_derivative_add
  map_smul' a p := iterate_derivative_smul _ _ _
#align polynomial.iterate_derivative_linear_map Polynomial.iterateDerivativeLinearMap

theorem iterateDerivativeLinearMap_apply (p : R[X]) (n : ℕ) :
    iterateDerivativeLinearMap n p = (derivative^[n]) p :=
  rfl
#align polynomial.iterate_derivative_linear_map_apply Polynomial.iterateDerivativeLinearMap_apply

variable (f p q : R[X]) (n k : ℕ)

theorem coeff_iterate_derivative_as_prod_range' :
    ∀ m : ℕ, ((derivative^[k]) f).coeff m = (∏ i in range k, (m + k - i)) • f.coeff (m + k) :=
  by
  induction' k with k ih
  · simp
  intro m
  calc
    ((derivative^[k.succ]) f).coeff m =
        (∏ i in range k, (m + k.succ - i)) • f.coeff (m + k.succ) * (m + 1) :=
      by rw [Function.iterate_succ_apply', coeff_derivative, ih m.succ, Nat.succ_add, Nat.add_succ]
    _ = ((∏ i in range k, (m + k.succ - i)) * (m + 1)) • f.coeff (m + k.succ) := by
      rw [← Nat.cast_add_one, ← nsmul_eq_mul', smul_smul, mul_comm]
    _ = (∏ i in range k.succ, (m + k.succ - i)) • f.coeff (m + k.succ) := by
      rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, Nat.succ_sub le_rfl, tsub_self]
#align polynomial.coeff_iterate_derivative_as_prod_range' Polynomial.coeff_iterate_derivative_as_prod_range'

theorem coeff_iterate_derivative_as_descFactorial (m : ℕ) :
    ((derivative^[k]) f).coeff m = (m + k).descFactorial k • f.coeff (m + k) := by
  rw [coeff_iterate_derivative_as_prod_range', ← Nat.descFactorial_eq_prod_range]
#align polynomial.coeff_iterate_derivative_as_desc_factorial Polynomial.coeff_iterate_derivative_as_descFactorial

end Semiring

section Ring

variable [Ring R]

theorem sumIderiv_sub (p : R[X]) : p.sumIderiv - p.derivative.sumIderiv = p := by
  rw [sum_ideriv_eq_self_add, add_sub_cancel]
#align polynomial.sum_ideriv_sub Polynomial.sumIderiv_sub

def sumIderivLinearEquiv : R[X] ≃ₗ[R] R[X] :=
  { sumIderiv with
    toFun := fun p => ∑ i in range (p.natDegree + 1), (derivative^[i]) p
    invFun := fun p => p - p.derivative
    left_inv := fun p => by simp_rw [← sum_ideriv_apply, ← sum_ideriv_derivative, sum_ideriv_sub]
    right_inv := fun p => by simp_rw [← sum_ideriv_apply, map_sub, sum_ideriv_sub] }
#align polynomial.sum_ideriv_linear_equiv Polynomial.sumIderivLinearEquiv

theorem sumIderivLinearEquiv_apply (p : R[X]) :
    p.sumIderivLinearEquiv = ∑ i in range (p.natDegree + 1), (derivative^[i]) p :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_apply Polynomial.sumIderivLinearEquiv_apply

theorem sumIderivLinearEquiv_symm_apply (p : R[X]) :
    sumIderivLinearEquiv.symm p = p - p.derivative :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_symm_apply Polynomial.sumIderivLinearEquiv_symm_apply

theorem sumIderivLinearEquiv_eq_sumIderiv (p : R[X]) : p.sumIderivLinearEquiv = p.sumIderiv :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_eq_sum_ideriv Polynomial.sumIderivLinearEquiv_eq_sumIderiv

end Ring

end Polynomial

open Polynomial

open scoped Nat

variable {R A : Type _} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

namespace Polynomial

theorem iterate_derivative_x_sub_c_pow (r : R) (k : ℕ) :
    ∀ n : ℕ, (derivative^[n]) ((X - C r) ^ k : R[X]) = k.descFactorial n • (X - C r) ^ (k - n)
  | 0 => by rw [Function.iterate_zero_apply, Nat.descFactorial, one_smul, tsub_zero]
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_derivative_X_sub_C_pow n, derivative_smul,
      derivative_X_sub_C_pow, Nat.descFactorial, C_eq_nat_cast, ← nsmul_eq_mul, smul_smul, mul_comm,
      tsub_tsub]
#align polynomial.iterate_derivative_X_sub_C_pow Polynomial.iterate_derivative_x_sub_c_pow

theorem natDegree_iterate_derivative (p : R[X]) (k : ℕ) :
    ((derivative^[k]) p).natDegree ≤ p.natDegree - k :=
  by
  induction' k with d hd; · rw [Function.iterate_zero_apply, Nat.sub_zero]
  rw [Function.iterate_succ_apply', Nat.sub_succ']
  refine' (nat_degree_derivative_le _).trans _
  exact Nat.sub_le_sub_right hd 1
#align polynomial.nat_degree_iterate_derivative Polynomial.natDegree_iterate_derivative

theorem iterate_derivative_eq_factorial_mul (p : R[X]) (k : ℕ) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - k), (derivative^[k]) p = k ! • gp :=
  by
  use ∑ x : ℕ in ((derivative^[k]) p).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x
  constructor
  · refine' (nat_degree_sum_le _ _).trans _
    rw [fold_max_le]
    refine' ⟨Nat.zero_le _, fun i hi => _⟩; dsimp only [Function.comp]
    replace hi := le_nat_degree_of_mem_supp _ hi
    rw [smul_C]; refine' (nat_degree_C_mul_le _ _).trans _
    rw [nat_degree_X_pow]; refine' hi.trans _
    exact nat_degree_iterate_derivative _ _
  conv_lhs => rw [((derivative^[k]) p).as_sum_support_C_mul_X_pow]
  rw [smul_sum]; congr; funext i
  calc
    C (((derivative^[k]) p).coeff i) * X ^ i =
        C ((i + k).descFactorial k • p.coeff (i + k)) * X ^ i :=
      by rw [coeff_iterate_derivative_as_desc_factorial]
    _ = C ((k ! * (i + k).choose k) • p.coeff (i + k)) * X ^ i := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
    _ = (k ! * (i + k).choose k) • C (p.coeff (i + k)) * X ^ i := by rw [smul_C]
    _ = k ! • (i + k).choose k • C (p.coeff (i + k)) * X ^ i := by rw [mul_smul]
    _ = k ! • ((i + k).choose k • C (p.coeff (i + k)) * X ^ i) := by rw [smul_mul_assoc]
#align polynomial.iterate_derivative_eq_factorial_mul Polynomial.iterate_derivative_eq_factorial_mul

theorem iterate_derivative_small (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : ℕ} (hk : k < q) :
    aeval r ((derivative^[k]) p) = 0 :=
  by
  have h : ∀ x, (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) :=
    by
    intro x; rw [← pow_add, add_tsub_cancel_of_le]; rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _)
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_C_pow, ← smul_mul_assoc, smul_smul,
    h, ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    MulZeroClass.zero_mul]
#align polynomial.iterate_derivative_small Polynomial.iterate_derivative_small

theorem iterate_derivative_of_eq (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') :
    aeval r ((derivative^[q]) p) = q ! • p'.eval r :=
  by
  have h :
    ∀ x ≥ 1, x ≤ q → (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    intro x h h'; rw [← pow_add, add_tsub_cancel_of_le]; rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_C_pow, ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ', Nat.choose_zero_right, one_mul, tsub_zero, Nat.descFactorial_self, tsub_self,
    pow_zero, smul_mul_assoc, one_mul, Function.iterate_zero, eval_add, eval_smul]
  convert zero_add _; rw [← coe_eval_ring_hom, map_sum]; apply sum_eq_zero; intro x hx
  rw [coe_eval_ring_hom, h (x + 1) le_add_self (nat.add_one_le_iff.mpr (mem_range.mp hx)), pow_one,
    eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, MulZeroClass.zero_mul,
    smul_zero, MulZeroClass.zero_mul]
#align polynomial.iterate_derivative_of_eq Polynomial.iterate_derivative_of_eq

variable (A)

theorem iterate_derivative_large (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - k),
      ∀ r : A, aeval r ((derivative^[k]) p) = q ! • aeval r gp :=
  by
  obtain ⟨p', p'_le, hp'⟩ := iterate_derivative_eq_factorial_mul p k
  refine' ⟨(k.desc_factorial (k - q) : ℤ) • p', _, _⟩
  · rw [zsmul_eq_mul, ← C_eq_int_cast]
    exact (nat_degree_C_mul_le _ _).trans p'_le
  intro r
  rw [hp', aeval_def, eval₂_eq_eval_map, nsmul_eq_mul, Polynomial.map_mul, Polynomial.map_nat_cast]
  rw [eval_mul, eval_nat_cast, ← Nat.factorial_mul_descFactorial (tsub_le_self : k - q ≤ k),
    tsub_tsub_cancel_of_le hk, Nat.cast_mul, mul_assoc]
  rw [aeval_def, eval₂_eq_eval_map, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_int_cast,
    eval_mul, eval_int_cast, Int.cast_ofNat, nsmul_eq_mul]
#align polynomial.iterate_derivative_large Polynomial.iterate_derivative_large

theorem sumIderiv_sl (p : R[X]) (q : ℕ) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (r : A) {p' : A[X]} (hp : p.map (algebraMap R A) = (X - C r) ^ q * p'),
        aeval r p.sumIderiv = q ! • aeval r gp :=
  by
  have h :
    ∀ k,
      ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.nat_degree - q),
        ∀ (r : A) {p' : A[X]} (hp : p.map (algebraMap R A) = (X - C r) ^ q * p'),
          aeval r ((derivative^[k]) p) = q ! • aeval r gp :=
    by
    intro k; cases' lt_or_ge k q with hk hk
    · use 0; rw [nat_degree_zero]; use Nat.zero_le _
      intro r p' hp; rw [map_zero, smul_zero, iterate_derivative_small p q r hp hk]
    · obtain ⟨gp, gp_le, h⟩ := iterate_derivative_large A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r p' hp => h r⟩
  let c k := (h k).some
  have c_le : ∀ k, (c k).natDegree ≤ p.nat_degree - q := fun k => (h k).choose_spec.some
  have hc :
    ∀ k,
      ∀ (r : A) {p' : A[X]} (hp : p.map (algebraMap R A) = (X - C r) ^ q * p'),
        aeval r ((derivative^[k]) p) = q ! • aeval r (c k) :=
    fun k => (h k).choose_spec.choose_spec
  refine' ⟨(range (p.nat_degree + 1)).Sum c, _, _⟩
  · refine' (nat_degree_sum_le _ _).trans _
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => c_le i⟩
  intro r p' hp
  rw [sum_ideriv_apply, map_sum]; simp_rw [hc _ r hp, map_sum, smul_sum]
#align polynomial.sum_ideriv_sl Polynomial.sumIderiv_sl

theorem sumIderiv_sl' (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (inj_amap : Function.Injective (algebraMap R A)) (r : A) {p' : A[X]}
        (hp : p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p'),
        aeval r p.sumIderiv = (q - 1)! • p'.eval r + q ! • aeval r gp :=
  by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0; rw [nat_degree_zero]; use Nat.zero_le _
    intro inj_amap r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]; rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left _
    rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (pow_eq_zero h)
  let c k := if hk : q ≤ k then (iterate_derivative_large A p q hk).some else 0
  have c_le : ∀ k, (c k).natDegree ≤ p.nat_degree - k := fun k =>
    by
    dsimp only [c]; split_ifs; · exact (iterate_derivative_large A p q h).choose_spec.some
    rw [nat_degree_zero]; exact Nat.zero_le _
  have hc : ∀ (k) (hk : q ≤ k) (r : A), aeval r ((derivative^[k]) p) = q ! • aeval r (c k) :=
    fun k hk => by simp_rw [c, dif_pos hk];
    exact (iterate_derivative_large A p q hk).choose_spec.choose_spec
  refine' ⟨∑ x : ℕ in Ico q (p.nat_degree + 1), c x, _, _⟩
  · refine' (nat_degree_sum_le _ _).trans _
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro inj_amap r p' hp
  have : range (p.nat_degree + 1) = range q ∪ Ico q (p.nat_degree + 1) :=
    by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    have h := nat_degree_map_le (algebraMap R A) p
    rw [congr_arg nat_degree hp, nat_degree_mul, nat_degree_pow, nat_degree_X_sub_C, mul_one, ←
      Nat.sub_add_comm (Nat.one_le_of_lt hq), tsub_le_iff_right] at h
    exact le_of_add_le_left h
    · exact pow_ne_zero _ (X_sub_C_ne_zero r)
    · rintro rfl; rw [MulZeroClass.mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp ;
      exact p0 hp
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sum_ideriv_apply, map_sum, map_sum, this, sum_union,
    (by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)] : range q = range (q - 1 + 1)),
    sum_range_succ]
  congr 1; congr 1
  · exact sum_eq_zero fun x hx => iterate_derivative_small p _ r hp (mem_range.mp hx)
  · rw [← iterate_derivative_of_eq _ _ _ hp]
  · rw [smul_sum, sum_congr rfl]; intro k hk; exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
    intro x hx; rw [mem_inter, mem_Ico, mem_Ico] at hx ; exact hx.1.2.not_le hx.2.1
#align polynomial.sum_ideriv_sl' Polynomial.sumIderiv_sl'

end Polynomial

open Complex

theorem DifferentiableAt.real_of_complex {e : ℂ → ℂ} {z : ℝ} (h : DifferentiableAt ℂ e ↑z) :
    DifferentiableAt ℝ (fun x : ℝ => e ↑x) z :=
  (h.restrictScalars ℝ).comp z ofRealClm.Differentiable.DifferentiableAt
#align differentiable_at.real_of_complex DifferentiableAt.real_of_complex

theorem Differentiable.real_of_complex {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ fun x : ℝ => e ↑x :=
  (h.restrictScalars ℝ).comp ofRealClm.Differentiable
#align differentiable.real_of_complex Differentiable.real_of_complex

theorem deriv_eq_f (p : ℂ[X]) (s : ℂ) :
    (deriv fun x : ℝ =>
        -(exp (-(x • exp (s.arg • I))) * p.sumIderiv.eval (x • exp (s.arg • I))) /
          exp (s.arg • I)) =
      fun x : ℝ => exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) :=
  by
  have h :
    (fun y : ℝ => p.sum_ideriv.eval (y • exp (s.arg • I))) =
      (fun x => p.sum_ideriv.eval x) ∘ fun y => y • exp (s.arg • I) :=
    rfl
  funext; rw [deriv_div_const, deriv.neg, deriv_mul, deriv_cexp, deriv.neg]
  any_goals simp_rw [h]; clear h
  rw [deriv_smul_const, deriv_id'', deriv.comp, Polynomial.deriv, deriv_smul_const, deriv_id'']
  simp_rw [derivative_map, one_smul, mul_assoc, ← mul_add]
  have h :
    exp (s.arg • I) * p.sum_ideriv.eval (x • exp (s.arg • I)) -
        p.sum_ideriv.derivative.eval (x • exp (s.arg • I)) * exp (s.arg • I) =
      p.eval (x • exp (s.arg • I)) * exp (s.arg • I) :=
    by
    conv_lhs =>
      congr
      rw [sum_ideriv_eq_self_add, sum_ideriv_derivative]
    rw [mul_comm, eval_add, add_mul, add_sub_cancel]
  rw [← mul_neg, neg_add', neg_mul, neg_neg, h, ← mul_assoc, mul_div_cancel]
  exact exp_ne_zero _
  any_goals apply Differentiable.differentiableAt
  rotate_left 5; apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * exp (s.arg • I)))
  rotate_left; apply Differentiable.comp; apply @Differentiable.restrictScalars ℝ _ ℂ
  any_goals
    repeat'
      first
      | apply Differentiable.neg
      | apply Differentiable.cexp
      | apply Differentiable.mul_const
      | apply Polynomial.differentiable
      | apply Differentiable.smul_const
      | exact differentiable_id
#align deriv_eq_f deriv_eq_f

theorem integral_f_eq (p : ℂ[X]) (s : ℂ) :
    ∫ x in 0 ..s.abs, exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) =
      -(exp (-s) * p.sumIderiv.eval s) / exp (s.arg • I) - -p.sumIderiv.eval 0 / exp (s.arg • I) :=
  by
  convert
    intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ =>
        -(exp (-(x • exp (s.arg • I))) * p.sum_ideriv.eval (x • exp (s.arg • I))) / exp (s.arg • I))
      (deriv_eq_f p s) _ _
  any_goals simp_rw [real_smul, abs_mul_exp_arg_mul_I]
  · simp_rw [zero_smul, neg_zero, Complex.exp_zero, one_mul]
  · intro x hx; apply ((Differentiable.mul _ _).neg.div_const _).DifferentiableAt
    apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * exp (s.arg • I)))
    refine' (differentiable_id.mul_const _).neg.cexp
    change Differentiable ℝ ((fun y : ℂ => p.sum_ideriv.eval y) ∘ fun x : ℝ => x • exp (s.arg • I))
    apply Differentiable.comp
    apply @Differentiable.restrictScalars ℝ _ ℂ; exact Polynomial.differentiable _
    exact differentiable_id'.smul_const _
  · refine' ((continuous_id'.smul continuous_const).neg.cexp.mul _).ContinuousOn
    change Continuous ((fun y : ℂ => p.eval y) ∘ fun x : ℝ => x • exp (s.arg • I))
    exact p.continuous_aeval.comp (continuous_id'.smul continuous_const)
#align integral_f_eq integral_f_eq

def p (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIderiv.eval 0 - p.sumIderiv.eval s
#align P p

theorem p_le' (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 s.abs, ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ, (p (p q) s).abs ≤ Real.exp s.re * (Real.exp s.abs * c ^ q * s.abs) :=
  by
  simp_rw [p]; cases' h with c hc; replace hc := fun q x hx => (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc ; use |c|, abs_nonneg _; intro q
  have h := integral_f_eq (p q) s
  rw [← sub_div, eq_div_iff (exp_ne_zero _), ← @mul_right_inj' _ _ (exp s) _ _ (exp_ne_zero _),
    neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add, add_neg_self, exp_zero, one_mul] at h
  replace h := congr_arg Complex.abs h
  simp_rw [map_mul, abs_exp, smul_re, I_re, smul_zero, Real.exp_zero, mul_one] at h
  rw [← h, mul_le_mul_left (Real.exp_pos _), ← Complex.norm_eq_abs,
    intervalIntegral.integral_of_le (complex.abs.nonneg _)]
  clear h
  convert MeasureTheory.norm_set_integral_le_of_norm_le_const' _ _ _
  · rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (complex.abs.nonneg _)]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  · exact measurableSet_Ioc
  intro x hx; rw [norm_mul]; refine' mul_le_mul _ (hc q x hx) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_eq_abs, abs_exp, Real.exp_le_exp]; apply (re_le_abs _).trans;
  rw [← norm_eq_abs, norm_neg, norm_smul, norm_eq_abs, abs_exp, smul_re, I_re, smul_zero,
    Real.exp_zero, mul_one, Real.norm_eq_abs, abs_eq_self.mpr hx.1.le]
  exact hx.2
#align P_le' p_le'

theorem p_le (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 s.abs, ((p q).eval (x • exp (s.arg • I))).abs ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q ≥ 1, (p (p q) s).abs ≤ c ^ q :=
  by
  simp_rw [p]; obtain ⟨c', hc', h'⟩ := p_le' p s h; clear h
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp s.abs) 1; have h₂ : 0 ≤ Real.exp s.abs := (Real.exp_pos _).le
  let c₃ := max s.abs 1; have h₃ : 0 ≤ s.abs := complex.abs.nonneg _
  have hc : ∀ {x : ℝ}, 0 ≤ max x 1 := fun x => zero_le_one.trans (le_max_right _ _)
  use c₁ * (c₂ * c' * c₃), mul_nonneg hc (mul_nonneg (mul_nonneg hc hc') hc)
  intro q hq; refine' (h' q).trans _; simp_rw [mul_pow]
  have hcq : ∀ {x : ℝ}, 0 ≤ max x 1 ^ q := fun x => pow_nonneg hc q
  have hcq' := pow_nonneg hc' q
  have le_max_one_pow : ∀ {x : ℝ}, x ≤ max x 1 ^ q := fun x =>
    (max_cases x 1).elim (fun h => h.1.symm ▸ le_self_pow h.2 (zero_lt_one.trans_le hq).ne')
      fun h => by rw [h.1, one_pow] <;> exact h.2.le
  refine' mul_le_mul le_max_one_pow _ (mul_nonneg (mul_nonneg h₂ hcq') h₃) hcq
  refine' mul_le_mul _ le_max_one_pow h₃ (mul_nonneg hcq hcq')
  refine' mul_le_mul le_max_one_pow le_rfl hcq' hcq
#align P_le p_le

open Polynomial

theorem exp_polynomial_approx (p : ℤ[X]) (p0 : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs,
        ∀ (prime_q : Nat.Prime q),
          ∃ (n : ℤ) (hn : n % q ≠ 0) (gp : ℤ[X]) (gp_le : gp.natDegree ≤ q * p.natDegree - 1),
            ∀ {r : ℂ} (hr : r ∈ p.aroots ℂ),
              (n • exp r - q • aeval r gp : ℂ).abs ≤ c ^ q / (q - 1)! :=
  by
  let p' q := (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ)
  have :
    ∀ s : ℂ,
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 s.abs, ((p' q).eval (x • exp (s.arg • I))).abs ≤ c ^ q :=
    by
    intro s; dsimp only [p']
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_exp_of_real_mul_I, abs_of_real, mul_one, ←
      eval₂_eq_eval_map, ← aeval_def]
    have :
      Metric.Bounded
        ((fun x => max |x| 1 * (aeval (↑x * exp (↑s.arg * I)) p).abs) '' Set.Ioc 0 (abs s)) :=
      by
      have h :
        (fun x => max |x| 1 * (aeval (↑x * exp (↑s.arg * I)) p).abs) '' Set.Ioc 0 (abs s) ⊆
          (fun x => max |x| 1 * (aeval (↑x * exp (↑s.arg * I)) p).abs) '' Set.Icc 0 (abs s) :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine' (IsCompact.image is_compact_Icc _).Bounded.mono h
      · refine' (continuous_id.abs.max continuous_const).mul _
        refine' complex.continuous_abs.comp (p.continuous_aeval.comp _)
        exact continuous_of_real.mul continuous_const
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max |x| 1 * (aeval (↑x * exp (↑s.arg * I)) p).abs) (Set.mem_image_of_mem _ hx)
    refine' le_trans _ (pow_le_pow_of_le_left (norm_nonneg _) h _)
    simp_rw [norm_mul, Real.norm_eq_abs, Complex.abs_abs, mul_pow]
    refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (complex.abs.nonneg _) _)
    rw [max_def]; split_ifs with hx1
    · rw [_root_.abs_one, one_pow]
      exact pow_le_one _ (abs_nonneg _) hx1
    · push_neg at hx1
      rw [_root_.abs_abs]; exact pow_le_pow hx1.le (Nat.sub_le _ _)
  let c' r := (p_le p' r (this r)).some
  have c'0 : ∀ r, 0 ≤ c' r := fun r => (p_le p' r (this r)).choose_spec.some
  have Pp'_le : ∀ (r : ℂ), ∀ q ≥ 1, abs (p (p' q) r) ≤ c' r ^ q := fun r =>
    (p_le p' r (this r)).choose_spec.choose_spec
  let c :=
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  have hc : ∀ x ∈ p.aroots ℂ, c' x ≤ c := by
    intro x hx; dsimp only [c]
    split_ifs
    · apply Finset.le_max'; rw [Multiset.mem_toFinset]
      refine' Multiset.mem_map_of_mem _ hx
    · rw [nonempty_iff_ne_empty, Ne.def, Multiset.toFinset_eq_empty,
        Multiset.eq_zero_iff_forall_not_mem] at h
      push_neg at h
      exact absurd (Multiset.mem_map_of_mem _ hx) (h (c' x))
  use c
  intro q q_gt prime_q
  have q0 : 0 < q := Nat.Prime.pos prime_q
  obtain ⟨gp', gp'_le, h'⟩ := sum_ideriv_sl' ℤ (X ^ (q - 1) * p ^ q) q0
  simp_rw [RingHom.algebraMap_toAlgebra, map_id] at h'
  specialize h' (RingHom.injective_int _) 0 (by rw [C_0, sub_zero])
  rw [eval_pow] at h'
  use p.eval 0 ^ q + q • aeval 0 gp'
  constructor
  · rw [Int.add_emod, nsmul_eq_mul, Int.mul_emod_right, add_zero, Int.emod_emod, Ne.def, ←
      Int.dvd_iff_emod_eq_zero]
    intro h
    replace h := Int.Prime.dvd_pow' prime_q h; rw [Int.coe_nat_dvd_left] at h
    replace h := Nat.le_of_dvd (Int.natAbs_pos_of_ne_zero p0) h
    revert h; rwa [imp_false, not_le]
  obtain ⟨gp, gp'_le, h⟩ := sum_ideriv_sl ℂ (X ^ (q - 1) * p ^ q) q
  refine' ⟨gp, _, _⟩
  · refine' gp'_le.trans ((tsub_le_tsub_right nat_degree_mul_le q).trans _)
    rw [nat_degree_X_pow, nat_degree_pow, tsub_add_eq_add_tsub (Nat.one_le_of_lt q0),
      tsub_right_comm]
    apply tsub_le_tsub_right; rw [add_tsub_cancel_left]
  intro r hr
  have :
    (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ) =
      (X - C r) ^ q *
        (X ^ (q - 1) *
          (C (map (algebraMap ℤ ℂ) p).leadingCoeff *
              (((p.aroots ℂ).eraseₓ r).map fun a : ℂ => X - C a).Prod) ^
            q) :=
    by
    rw [mul_left_comm, ← mul_pow, mul_left_comm (_ - _), Multiset.prod_map_erase hr]
    have : (p.aroots ℂ).card = (p.map (algebraMap ℤ ℂ)).natDegree :=
      splits_iff_card_roots.mp (IsAlgClosed.splits _)
    rw [C_leading_coeff_mul_prod_multiset_X_sub_C this, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, map_X]
  specialize h r this; clear this
  rw [le_div_iff (nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_of_nat, ← map_mul,
    mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul, mul_comm,
    Nat.mul_factorial_pred q0, ← h]
  rw [nsmul_eq_mul, ← Int.cast_ofNat, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul, ←
    nsmul_eq_mul, smul_smul, mul_comm, Nat.mul_factorial_pred q0, ← h', zsmul_eq_mul, aeval_def,
    eval₂_at_zero, eq_intCast, Int.cast_id, ← Int.coe_castRingHom, ← algebraMap_int_eq, ←
    eval₂_at_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, mul_comm, ← sum_ideriv_map, ← p]
  exact (Pp'_le r q (Nat.one_le_of_lt q0)).trans (pow_le_pow_of_le_left (c'0 r) (hc r hr) _)
#align exp_polynomial_approx exp_polynomial_approx

namespace AddMonoidAlgebra

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr finsupp.sum x (λ g1 r1, _)]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr finsupp.sum y (λ g2 r2, _)]] -/
@[simps]
def ringEquivCongrLeft {R S G : Type _} [Semiring R] [Semiring S] [AddMonoid G] (f : R ≃+* S) :
    AddMonoidAlgebra R G ≃+* AddMonoidAlgebra S G :=
  {
    Finsupp.mapRange.addEquiv
      f.toAddEquiv with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    invFun :=
      (Finsupp.mapRange f.symm f.symm.map_zero : AddMonoidAlgebra S G → AddMonoidAlgebra R G)
    map_mul' := fun x y => by
      ext; simp_rw [mul_apply, mul_def, Finsupp.mapRange_apply, Finsupp.sum_apply, map_finsupp_sum]
      rw [Finsupp.sum_mapRange_index];
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr finsupp.sum x (λ g1 r1, _)]]"
      rw [Finsupp.sum_mapRange_index];
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr finsupp.sum y (λ g2 r2, _)]]"
      · rw [Finsupp.single_apply]; split_ifs <;> simp only [map_mul, map_zero]; contradiction
      all_goals intro; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul];
        simp only [if_t_t, Finsupp.sum_zero] }
#align add_monoid_algebra.ring_equiv_congr_left AddMonoidAlgebra.ringEquivCongrLeft

@[simps]
def algEquivCongrLeft {k R S G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] (f : R ≃ₐ[k] S) : AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra S G :=
  {
    ringEquivCongrLeft
      f.toRingEquiv with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    invFun :=
      (Finsupp.mapRange f.symm f.symm.map_zero : AddMonoidAlgebra S G → AddMonoidAlgebra R G)
    commutes' := fun r => by
      ext
      simp_rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.mapRange_single]
      congr 2
      change f.to_alg_hom ((algebraMap k R) r) = (algebraMap k S) r
      rw [AlgHom.map_algebraMap] }
#align add_monoid_algebra.alg_equiv_congr_left AddMonoidAlgebra.algEquivCongrLeft

@[simps]
def algAutCongrLeft {k R G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [AddMonoid G] :
    (R ≃ₐ[k] R) →* AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra R G
    where
  toFun f := algEquivCongrLeft f
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl
#align add_monoid_algebra.alg_aut_congr_left AddMonoidAlgebra.algAutCongrLeft

@[simps]
def mapDomainRingEquiv (k : Type _) [Semiring k] {G H : Type _} [AddMonoid G] [AddMonoid H]
    (f : G ≃+ H) : AddMonoidAlgebra k G ≃+* AddMonoidAlgebra k H :=
  { Finsupp.domCongr f.toEquiv with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    map_mul' := fun x y => by
      simp_rw [← Finsupp.domCongr_apply]
      induction x using Finsupp.induction_linear
      · simp only [map_zero, MulZeroClass.zero_mul]; · simp only [add_mul, map_add, *]
      induction y using Finsupp.induction_linear <;>
        simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, map_zero, mul_add, map_add, *]
      ext;
      simp only [Finsupp.domCongr_apply, single_mul_single, Finsupp.equivMapDomain_single,
        AddEquiv.coe_toEquiv, map_add] }
#align add_monoid_algebra.map_domain_ring_equiv AddMonoidAlgebra.mapDomainRingEquiv

@[simps]
def mapDomainAlgEquiv (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G H : Type _}
    [AddMonoid G] [AddMonoid H] (f : G ≃+ H) : AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A H :=
  { mapDomainRingEquiv A f with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    commutes' := fun r => by
      simp only [Function.comp_apply, Finsupp.equivMapDomain_single,
        AddMonoidAlgebra.coe_algebraMap, map_zero, AddEquiv.coe_toEquiv] }
#align add_monoid_algebra.map_domain_alg_equiv AddMonoidAlgebra.mapDomainAlgEquiv

@[simps]
def mapDomainAlgAut (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G : Type _}
    [AddMonoid G] : AddAut G →* AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A G
    where
  toFun := mapDomainAlgEquiv k A
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl
#align add_monoid_algebra.map_domain_alg_aut AddMonoidAlgebra.mapDomainAlgAut

end AddMonoidAlgebra

namespace Aux

variable (p : ℚ[X])

abbrev k' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (p.rootSet ℂ)
#align aux.K' Aux.k'

instance k'.isSplittingField : IsSplittingField ℚ (k' p) p :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain p)
#align aux.K'.is_splitting_field Aux.k'.isSplittingField

abbrev K : Type _ :=
  p.SplittingField
#align aux.K Aux.K

instance : CharZero (K p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (K p)).Injective

instance : IsGalois ℚ (K p) where

abbrev lift : k' p ≃ₐ[ℚ] K p :=
  IsSplittingField.algEquiv (k' p) p
#align aux.Lift Aux.lift

instance algebraKℂ : Algebra (K p) ℂ :=
  ((k' p).val.comp (lift p).symm.toAlgHom).toRingHom.toAlgebra
#align aux.algebra_K_ℂ Aux.algebraKℂ

/-- ```
example : (intermediate_field.to_algebra _ : algebra (⊥ : intermediate_field ℚ (K p)) (K p)) =
  (splitting_field.algebra' p : algebra (⊥ : intermediate_field ℚ (K p)) (K p)) :=
rfl
```
-/
instance avoidDiamondCache : Algebra (⊥ : IntermediateField ℚ (K p)) (K p) :=
  IntermediateField.toAlgebra _
#align aux.avoid_diamond_cache Aux.avoidDiamondCache

/-- example : algebra_int (K p) = (infer_instance : algebra ℤ (K p)) := rfl
-/
instance avoidDiamondIntCache : Algebra ℤ (K p) :=
  algebraInt (K p)
#align aux.avoid_diamond_int_cache Aux.avoidDiamondIntCache

instance : Algebra ℚ (K p) :=
  inferInstance

instance : SMul ℚ (K p) :=
  Algebra.toHasSmul

instance cache_ℚ_k_ℂ : IsScalarTower ℚ (K p) ℂ :=
  inferInstance
#align aux.cache_ℚ_K_ℂ Aux.cache_ℚ_k_ℂ

instance cache_ℤ_k_ℂ : IsScalarTower ℤ (K p) ℂ :=
  inferInstance
#align aux.cache_ℤ_K_ℂ Aux.cache_ℤ_k_ℂ

end Aux

namespace Quot

@[reducible, elab_as_elim]
protected def liftFinsupp {α : Type _} {r : α → α → Prop} {β : Type _} [Zero β] (f : α →₀ β)
    (h : ∀ a b, r a b → f a = f b) : Quot r →₀ β :=
  by
  refine' ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨_, a.ind fun b => _⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact finsupp.mem_support_iff.mp hb
  · rw [lift_mk _ h]; refine' fun hb => mem_image_of_mem _ (finsupp.mem_support_iff.mpr hb)
#align quot.lift_finsupp Quot.liftFinsupp

theorem liftFinsupp_mk {α : Type _} {r : α → α → Prop} {γ : Type _} [Zero γ] (f : α →₀ γ)
    (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_finsupp_mk Quot.liftFinsupp_mk

end Quot

namespace Quotient

@[reducible, elab_as_elim]
protected def liftFinsupp {α : Type _} {β : Type _} [s : Setoid α] [Zero β] (f : α →₀ β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s →₀ β :=
  Quot.liftFinsupp f
#align quotient.lift_finsupp Quotient.liftFinsupp

@[simp]
theorem liftFinsupp_mk' {α : Type _} {β : Type _} [s : Setoid α] [Zero β] (f : α →₀ β)
    (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) : Quotient.liftFinsupp f h (Quotient.mk' x) = f x :=
  rfl
#align quotient.lift_finsupp_mk Quotient.liftFinsupp_mk'

end Quotient

section

variable (s : Finset ℂ)

abbrev poly : ℚ[X] :=
  ∏ x in s, minpoly ℚ x
#align Poly poly

abbrev k' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((poly s).rootSet ℂ)
#align K' k'

abbrev K : Type _ :=
  (poly s).SplittingField
#align K K

abbrev Gal : Type _ :=
  (poly s).Gal
#align Gal Gal

/- warning: Lift clashes with lift -> lift
Case conversion may be inaccurate. Consider using '#align Lift liftₓ'. -/
#print lift /-
abbrev lift : k' s ≃ₐ[ℚ] K s :=
  IsSplittingField.algEquiv (k' s) (poly s)
#align Lift lift
-/

theorem algebraMap_k_apply (x) : algebraMap (K s) ℂ x = ((lift s).symm x : ℂ) :=
  rfl
#align algebra_map_K_apply algebraMap_k_apply

theorem poly_ne_zero (hs : ∀ x ∈ s, IsIntegral ℚ x) : poly s ≠ 0 :=
  prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)
#align Poly_ne_zero poly_ne_zero

noncomputable def ratCoeff : Subalgebra ℚ (AddMonoidAlgebra (K s) (K s))
    where
  carrier x := ∀ i : K s, x i ∈ (⊥ : IntermediateField ℚ (K s))
  mul_mem' a b ha hb i := by
    rw [AddMonoidAlgebra.mul_apply]
    refine' sum_mem fun c hc => sum_mem fun d hd => _
    dsimp only; split_ifs; exacts [mul_mem (ha c) (hb d), zero_mem _]
  add_mem' a b ha hb i := by rw [Finsupp.add_apply]; exact add_mem (ha i) (hb i)
  algebraMap_mem' r hr :=
    by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.single_apply]
    split_ifs; exacts [IntermediateField.algebraMap_mem _ _, zero_mem _]
#align rat_coeff ratCoeff

--cache
instance : ZeroMemClass (IntermediateField ℚ (K s)) (K s) :=
  inferInstance

def RatCoeffEquiv.aux : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra (⊥ : IntermediateField ℚ (K s)) (K s)
    where
  toFun x :=
    { support := (x : AddMonoidAlgebra (K s) (K s)).support
      toFun := fun i => ⟨x i, x.2 i⟩
      mem_support_toFun := fun i => by
        rw [Finsupp.mem_support_iff]
        have : (0 : (⊥ : IntermediateField ℚ (K s))) = ⟨0, ZeroMemClass.zero_mem _⟩ := rfl
        simp_rw [this, Ne.def, Subtype.mk.inj_eq]; rfl }
  invFun x :=
    ⟨⟨x.support, fun i => x i, fun i => by
        simp_rw [Finsupp.mem_support_iff, Ne.def, ZeroMemClass.coe_eq_zero]⟩,
      fun i => SetLike.coe_mem _⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by
    ext; change (x * y : AddMonoidAlgebra (K s) (K s)) a = _
    simp_rw [AddMonoidAlgebra.mul_apply, Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine' sum_congr rfl fun i hi => sum_congr rfl fun j hj => _
    split_ifs <;> rfl
  map_add' x y := by
    ext; change (x + y : AddMonoidAlgebra (K s) (K s)) a = x a + y a
    rw [Finsupp.add_apply]; rfl
  commutes' x := by
    ext
    change
      (algebraMap ℚ (ratCoeff s) x) a =
        (Finsupp.single 0 (algebraMap ℚ (⊥ : IntermediateField ℚ (K s)) x)) a
    simp_rw [Algebra.algebraMap_eq_smul_one]
    change (x • Finsupp.single 0 (1 : K s)) a = _
    simp_rw [Finsupp.smul_single, Finsupp.single_apply]
    split_ifs <;> rfl
#align rat_coeff_equiv.aux RatCoeffEquiv.aux

def ratCoeffEquiv : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra ℚ (K s) :=
  (RatCoeffEquiv.aux s).trans
    (AddMonoidAlgebra.algEquivCongrLeft (IntermediateField.botEquiv ℚ (K s)))
#align rat_coeff_equiv ratCoeffEquiv

theorem ratCoeffEquiv_apply_apply (x : ratCoeff s) (i : K s) :
    ratCoeffEquiv s x i = (IntermediateField.botEquiv ℚ (K s)) ⟨x i, x.2 i⟩ :=
  rfl
#align rat_coeff_equiv_apply_apply ratCoeffEquiv_apply_apply

theorem support_ratCoeffEquiv (x : ratCoeff s) :
    (ratCoeffEquiv s x).support = (x : AddMonoidAlgebra (K s) (K s)).support :=
  by
  dsimp [ratCoeffEquiv, RatCoeffEquiv.aux]
  rw [Finsupp.support_mapRange_of_injective]
  exact AlgEquiv.injective _
#align support_rat_coeff_equiv support_ratCoeffEquiv

section

variable (F : Type _) [Field F] [Algebra ℚ F]

noncomputable def mapDomainFixed : Subalgebra F (AddMonoidAlgebra F (K s))
    where
  carrier x := ∀ f : Gal s, AddMonoidAlgebra.mapDomainAlgAut ℚ _ f.toAddEquiv x = x
  mul_mem' a b ha hb f := by rw [map_mul, ha, hb]
  add_mem' a b ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f :=
    by
    change Finsupp.equivMapDomain f.to_equiv (Finsupp.single _ _) = Finsupp.single _ _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (f 0) _ = _; rw [AlgEquiv.map_zero]
#align map_domain_fixed mapDomainFixed

theorem mem_mapDomainFixed_iff (x : AddMonoidAlgebra F (K s)) :
    x ∈ mapDomainFixed s F ↔ ∀ i j, i ∈ MulAction.orbit (Gal s) j → x i = x j :=
  by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : Gal s, Finsupp.equivMapDomain (↑(AlgEquiv.toAddEquiv f)) x = x) ↔ _
  refine' ⟨fun h i j hij => _, fun h f => _⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← Finsupp.congr_fun (h f) (f j)]
    change x (f.symm (f j)) = _; rw [AlgEquiv.symm_apply_apply]
  · ext i; change x (f.symm i) = x i
    refine' (h i ((AlgEquiv.symm f) i) ⟨f, _⟩).symm
    rw [AlgEquiv.smul_def, AlgEquiv.apply_symm_apply]
#align mem_map_domain_fixed_iff mem_mapDomainFixed_iff

noncomputable def mapDomainFixedEquivSubtype :
    mapDomainFixed s F ≃
      { f : AddMonoidAlgebra F (K s) // MulAction.orbitRel (Gal s) (K s) ≤ Setoid.ker f }
    where
  toFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mp f.2⟩
  invFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mpr f.2⟩
  left_inv f := by simp_rw [← Subtype.coe_inj, Subtype.coe_mk]
  right_inv f := by simp_rw [← Subtype.coe_inj, Subtype.coe_mk]
#align map_domain_fixed_equiv_subtype mapDomainFixedEquivSubtype

end
