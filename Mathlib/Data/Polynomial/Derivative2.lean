
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.Data.Polynomial.AlgebraMap

open scoped BigOperators Polynomial Nat
open Finset

namespace Nat

theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i in range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ, mul_comm, descFactorial_eq_prod_range n k]
#align nat.desc_factorial_eq_prod_range Nat.descFactorial_eq_prod_range

end Nat

namespace Polynomial


variable {R : Type _}

section Semiring

variable [Semiring R]

theorem sum_ideriv_apply_of_lt' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    ∑ i in range (p.natDegree + 1), derivative^[i] p = ∑ i in range n, derivative^[i] p :=
  by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hn; rw [hm, add_right_comm]
  rw [sum_range_add _ _ m]; convert (add_zero _).symm; apply sum_eq_zero
  intro x _; rw [add_comm, Function.iterate_add_apply]
  convert iterate_derivative_zero; rw [iterate_derivative_eq_zero]; exact lt_add_one _
#align polynomial.sum_ideriv_apply_of_lt' Polynomial.sum_ideriv_apply_of_lt'

theorem sum_ideriv_apply_of_le' {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    ∑ i in range (p.natDegree + 1), (derivative^[i]) p = ∑ i in range (n + 1), (derivative^[i]) p :=
  sum_ideriv_apply_of_lt' (Nat.lt_add_one_iff.mpr hn)
#align polynomial.sum_ideriv_apply_of_le' Polynomial.sum_ideriv_apply_of_le'

noncomputable def sumIderiv : R[X] →ₗ[R] R[X]
    where
  toFun p := ∑ i in range (p.natDegree + 1), (derivative^[i]) p
  map_add' p q :=
    by
    let x := max ((p + q).natDegree + 1) (max (p.natDegree + 1) (q.natDegree + 1))
    have hpq : (p + q).natDegree + 1 ≤ x := le_max_left _ _
    have hp : p.natDegree + 1 ≤ x := (le_max_left _ _).trans (le_max_right _ _)
    have hq : q.natDegree + 1 ≤ x := (le_max_right _ _).trans (le_max_right _ _)
    dsimp only
    rw [Nat.add_one_le_iff] at hpq hp hq
    simp_rw [sum_ideriv_apply_of_lt' hpq, sum_ideriv_apply_of_lt' hp, sum_ideriv_apply_of_lt' hq, ←
      sum_add_distrib, iterate_map_add]
  map_smul' a p := by
    dsimp only
    simp_rw [RingHom.id_apply, sum_ideriv_apply_of_le' (natDegree_smul_le _ _),
      iterate_derivative_smul, smul_sum]
#align polynomial.sum_ideriv Polynomial.sumIderiv

theorem sumIderiv_apply (p : R[X]) :
    sumIderiv p = ∑ i in range (p.natDegree + 1), (derivative^[i]) p :=
  rfl
#align polynomial.sum_ideriv_apply Polynomial.sumIderiv_apply

theorem sumIderiv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    sumIderiv p = ∑ i in range n, (derivative^[i]) p :=
  sum_ideriv_apply_of_lt' hn
#align polynomial.sum_ideriv_apply_of_lt Polynomial.sumIderiv_apply_of_lt

theorem sumIderiv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    sumIderiv p = ∑ i in range (n + 1), (derivative^[i]) p :=
  sum_ideriv_apply_of_le' hn
#align polynomial.sum_ideriv_apply_of_le Polynomial.sumIderiv_apply_of_le

theorem sumIderiv_C (a : R) : sumIderiv (C a) = C a := by
  rw [sumIderiv_apply, natDegree_C, zero_add, sum_range_one, Function.iterate_zero_apply]
set_option linter.uppercaseLean3 false in
#align polynomial.sum_ideriv_C Polynomial.sumIderiv_C

@[simp]
theorem sumIderiv_map {S : Type _} [CommSemiring S] (p : R[X]) (f : R →+* S) :
    sumIderiv (p.map f) = (sumIderiv p).map f :=
  by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIderiv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [sumIderiv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum]
  apply sum_congr rfl; intro x _
  rw [iterate_derivative_map p f x]
#align polynomial.sum_ideriv_map Polynomial.sumIderiv_map

theorem sumIderiv_derivative (p : R[X]) : sumIderiv (derivative p) = derivative (sumIderiv p) :=
  by
  rw [sumIderiv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self), sumIderiv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
#align polynomial.sum_ideriv_derivative Polynomial.sumIderiv_derivative

theorem sumIderiv_eq_self_add (p : R[X]) : sumIderiv p = p + sumIderiv (derivative p) :=
  by
  rw [sumIderiv_derivative, sumIderiv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative]; congr
  rw [iterate_derivative_eq_zero (Nat.lt_succ_self _)]
#align polynomial.sum_ideriv_eq_self_add Polynomial.sumIderiv_eq_self_add

noncomputable def iterateDerivativeLinearMap (n : ℕ) : R[X] →ₗ[R] R[X]
    where
  toFun p := (derivative^[n]) p
  map_add' p q := iterate_map_add _ _ p q
  map_smul' a p := iterate_derivative_smul a p _
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

theorem natDegree_iterate_derivative (p : R[X]) (k : ℕ) :
    ((derivative^[k]) p).natDegree ≤ p.natDegree - k :=
  by
  induction' k with d hd; · rw [Function.iterate_zero_apply, Nat.sub_zero]
  rw [Function.iterate_succ_apply', Nat.sub_succ']
  refine' (natDegree_derivative_le _).trans _
  exact Nat.sub_le_sub_right hd 1
#align polynomial.nat_degree_iterate_derivative Polynomial.natDegree_iterate_derivative

end Semiring

section Ring

variable [Ring R]

theorem sumIderiv_sub (p : R[X]) : sumIderiv p - sumIderiv (derivative p) = p := by
  rw [sumIderiv_eq_self_add, add_sub_cancel]
#align polynomial.sum_ideriv_sub Polynomial.sumIderiv_sub

noncomputable def sumIderivLinearEquiv : R[X] ≃ₗ[R] R[X] :=
  { sumIderiv with
    toFun := fun p => ∑ i in range (p.natDegree + 1), (derivative^[i]) p
    invFun := fun p => p - derivative p
    left_inv := fun p => by simp_rw [← sumIderiv_apply, ← sumIderiv_derivative, sumIderiv_sub]
    right_inv := fun p => by simp_rw [← sumIderiv_apply, map_sub, sumIderiv_sub] }
#align polynomial.sum_ideriv_linear_equiv Polynomial.sumIderivLinearEquiv

theorem sumIderivLinearEquiv_apply (p : R[X]) :
    sumIderivLinearEquiv p = ∑ i in range (p.natDegree + 1), (derivative^[i]) p :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_apply Polynomial.sumIderivLinearEquiv_apply

theorem sumIderivLinearEquiv_symm_apply (p : R[X]) :
    sumIderivLinearEquiv.symm p = p - derivative p :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_symm_apply Polynomial.sumIderivLinearEquiv_symm_apply

theorem sumIderivLinearEquiv_eq_sumIderiv (p : R[X]) : sumIderivLinearEquiv p = sumIderiv p :=
  rfl
#align polynomial.sum_ideriv_linear_equiv_eq_sum_ideriv Polynomial.sumIderivLinearEquiv_eq_sumIderiv

end Ring

section CommRing

variable [CommRing R]

theorem iterate_derivative_X_sub_pow' (r : R) (k n : ℕ) :
    (derivative^[n]) ((X - C r) ^ k : R[X]) = k.descFactorial n • (X - C r) ^ (k - n) := by
  rw [iterate_derivative_X_sub_pow, Nat.descFactorial_eq_prod_range, nsmul_eq_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.iterate_derivative_X_sub_C_pow Polynomial.iterate_derivative_X_sub_pow'

theorem iterate_derivative_eq_factorial_mul (p : R[X]) (k : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧ (derivative^[k]) p = k ! • gp :=
  by
  use ∑ x : ℕ in ((derivative^[k]) p).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x
  constructor
  · refine' (natDegree_sum_le _ _).trans _
    rw [fold_max_le]
    refine' ⟨Nat.zero_le _, fun i hi => _⟩; dsimp only [Function.comp]
    replace hi := le_natDegree_of_mem_supp _ hi
    rw [smul_C]; refine' (natDegree_C_mul_le _ _).trans _
    refine (natDegree_X_pow_le _).trans ?_
    refine' hi.trans _
    exact natDegree_iterate_derivative _ _
  conv_lhs => rw [((derivative^[k]) p).as_sum_support_C_mul_X_pow]
  rw [smul_sum]; congr; funext i
  calc
    C (((derivative^[k]) p).coeff i) * X ^ i =
        C ((i + k).descFactorial k • p.coeff (i + k)) * X ^ i :=
      by rw [coeff_iterate_derivative_as_descFactorial]
    _ = C ((k ! * (i + k).choose k) • p.coeff (i + k)) * X ^ i := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
    _ = (k ! * (i + k).choose k) • C (p.coeff (i + k)) * X ^ i := by rw [smul_C]
    _ = k ! • (i + k).choose k • C (p.coeff (i + k)) * X ^ i := by rw [mul_smul]
    _ = k ! • ((i + k).choose k • C (p.coeff (i + k)) * X ^ i) := by rw [smul_mul_assoc]
#align polynomial.iterate_derivative_eq_factorial_mul Polynomial.iterate_derivative_eq_factorial_mul

variable {A : Type _} [CommRing A] [Algebra R A]

theorem iterate_derivative_small (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : ℕ} (hk : k < q) :
    aeval r ((derivative^[k]) p) = 0 :=
  by
  have h : ∀ x, (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) :=
    by
    intro x; rw [← pow_add, add_tsub_cancel_of_le]; rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _)
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow', ← smul_mul_assoc, smul_smul,
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
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow', ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ', Nat.choose_zero_right, one_mul, tsub_zero, Nat.descFactorial_self, tsub_self,
    pow_zero, smul_mul_assoc, one_mul, Function.iterate_zero, eval_add, eval_smul]
  convert zero_add _; rw [← coe_evalRingHom, map_sum]; apply sum_eq_zero; intro x hx
  rw [coe_evalRingHom, h (x + 1) le_add_self (Nat.add_one_le_iff.mpr (mem_range.mp hx)), pow_one,
    eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, MulZeroClass.zero_mul,
    smul_zero, MulZeroClass.zero_mul]
#align polynomial.iterate_derivative_of_eq Polynomial.iterate_derivative_of_eq

variable (A)

theorem iterate_derivative_large (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧
      ∀ r : A, aeval r ((derivative^[k]) p) = q ! • aeval r gp :=
  by
  obtain ⟨p', p'_le, hp'⟩ := iterate_derivative_eq_factorial_mul p k
  refine' ⟨(k.descFactorial (k - q) : ℤ) • p', _, _⟩
  · rw [zsmul_eq_mul, ← C_eq_int_cast]
    exact (natDegree_C_mul_le _ _).trans p'_le
  intro r
  rw [hp', aeval_def, eval₂_eq_eval_map, nsmul_eq_mul, Polynomial.map_mul, Polynomial.map_nat_cast]
  rw [eval_mul, eval_nat_cast, ← Nat.factorial_mul_descFactorial (tsub_le_self : k - q ≤ k),
    tsub_tsub_cancel_of_le hk, Nat.cast_mul, mul_assoc]
  rw [aeval_def, eval₂_eq_eval_map, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_int_cast,
    eval_mul, eval_int_cast, Int.cast_ofNat, nsmul_eq_mul]
  simp only [ge_iff_le, Nat.cast_mul, mul_assoc, Int.cast_ofNat]
#align polynomial.iterate_derivative_large Polynomial.iterate_derivative_large

theorem sumIderiv_sl (p : R[X]) (q : ℕ) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (r : A) {p' : A[X]}, p.map (algebraMap R A) = (X - C r) ^ q * p' →
        aeval r (sumIderiv p) = q ! • aeval r gp :=
  by
  have h :
    ∀ k,
      ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
        ∀ (r : A) {p' : A[X]}, p.map (algebraMap R A) = (X - C r) ^ q * p' →
          aeval r ((derivative^[k]) p) = q ! • aeval r gp :=
    by
    intro k; cases' lt_or_ge k q with hk hk
    · use 0; rw [natDegree_zero]; use Nat.zero_le _
      intro r p' hp; rw [map_zero, smul_zero, iterate_derivative_small p q r hp hk]
    · obtain ⟨gp, gp_le, h⟩ := iterate_derivative_large A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r p' _ => h r⟩
  let c k := (h k).choose
  have c_le : ∀ k, (c k).natDegree ≤ p.natDegree - q := fun k => (h k).choose_spec.choose
  have hc :
    ∀ k,
      ∀ (r : A) {p' : A[X]}, p.map (algebraMap R A) = (X - C r) ^ q * p' →
        aeval r ((derivative^[k]) p) = q ! • aeval r (c k) :=
    fun k => (h k).choose_spec.choose_spec
  refine' ⟨(range (p.natDegree + 1)).sum c, _, _⟩
  · refine' (natDegree_sum_le _ _).trans _
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r p' hp
  rw [sumIderiv_apply, map_sum]; simp_rw [hc _ r hp, map_sum, smul_sum]
#align polynomial.sum_ideriv_sl Polynomial.sumIderiv_sl

theorem sumIderiv_sl' [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (inj_amap : Function.Injective (algebraMap R A)) (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' →
        aeval r (sumIderiv p) = (q - 1)! • p'.eval r + q ! • aeval r gp :=
  by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0; rw [natDegree_zero]; use Nat.zero_le _
    intro _ r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]; rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (pow_eq_zero h)
  let c k := if hk : q ≤ k then (iterate_derivative_large A p q hk).choose else 0
  have c_le : ∀ k, (c k).natDegree ≤ p.natDegree - k := fun k =>
    by
    dsimp only; split_ifs with h; · exact (iterate_derivative_large A p q h).choose_spec.1
    rw [natDegree_zero]; exact Nat.zero_le _
  have hc : ∀ (k) (_ : q ≤ k) (r : A), aeval r ((derivative^[k]) p) = q ! • aeval r (c k) :=
    fun k hk => by
      simp_rw [dif_pos hk]
      exact (iterate_derivative_large A p q hk).choose_spec.2
  refine' ⟨∑ x : ℕ in Ico q (p.natDegree + 1), c x, _, _⟩
  · refine' (natDegree_sum_le _ _).trans _
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro inj_amap r p' hp
  have : range (p.natDegree + 1) = range q ∪ Ico q (p.natDegree + 1) :=
    by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    have h := natDegree_map_le (algebraMap R A) p
    rw [congr_arg natDegree hp, natDegree_mul, natDegree_pow, natDegree_X_sub_C, mul_one, ←
      Nat.sub_add_comm (Nat.one_le_of_lt hq), tsub_le_iff_right] at h
    exact le_of_add_le_left h
    · exact pow_ne_zero _ (X_sub_C_ne_zero r)
    · rintro rfl; rw [MulZeroClass.mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp ;
      exact p0 hp
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sumIderiv_apply, map_sum, map_sum, this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union, this, sum_range_succ]
  rw [sum_union, sum_range_succ] -- why do we need to do this again?
  congr 1; congr 1
  · apply sum_eq_zero
    exact fun x hx => iterate_derivative_small p _ r hp (mem_range.mp hx)
  · rw [← iterate_derivative_of_eq _ _ _ hp]
  · rw [smul_sum, sum_congr rfl]; intro k hk; exact hc k (mem_Ico.mp hk).1 r
  all_goals
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
    intro x hx; rw [mem_inter, mem_Ico, mem_Ico] at hx
    try rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)] at hx
    exact hx.1.2.not_le hx.2.1
#align polynomial.sum_ideriv_sl' Polynomial.sumIderiv_sl'

end CommRing

end Polynomial
