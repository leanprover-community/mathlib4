/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Analysis.Complex.Arg

#align_import ring_theory.polynomial.cyclotomic.eval from "leanprover-community/mathlib"@"5bfbcca0a7ffdd21cf1682e59106d6c942434a32"

/-!
# Evaluating cyclotomic polynomials
This file states some results about evaluating cyclotomic polynomials in various different ways.
## Main definitions
* `Polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `Polynomial.eval_one_cyclotomic_not_prime_pow`: Otherwise, `eval 1 (cyclotomic n R) = 1`.
* `Polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/


namespace Polynomial

open Finset Nat

open scoped BigOperators

@[simp]
theorem eval_one_cyclotomic_prime {R : Type*} [CommRing R] {p : ℕ} [hn : Fact p.Prime] :
    eval 1 (cyclotomic p R) = p := by
  simp only [cyclotomic_prime, eval_X, one_pow, Finset.sum_const, eval_pow, eval_finset_sum,
    Finset.card_range, smul_one_eq_coe]
#align polynomial.eval_one_cyclotomic_prime Polynomial.eval_one_cyclotomic_prime

-- @[simp] -- Porting note: simp already proves this
theorem eval₂_one_cyclotomic_prime {R S : Type*} [CommRing R] [Semiring S] (f : R →+* S) {p : ℕ}
    [Fact p.Prime] : eval₂ f 1 (cyclotomic p R) = p := by simp
#align polynomial.eval₂_one_cyclotomic_prime Polynomial.eval₂_one_cyclotomic_prime

@[simp]
theorem eval_one_cyclotomic_prime_pow {R : Type*} [CommRing R] {p : ℕ} (k : ℕ)
    [hn : Fact p.Prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p := by
  simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, Finset.sum_const, eval_pow,
    eval_finset_sum, Finset.card_range, smul_one_eq_coe]
#align polynomial.eval_one_cyclotomic_prime_pow Polynomial.eval_one_cyclotomic_prime_pow

-- @[simp] -- Porting note: simp already proves this
theorem eval₂_one_cyclotomic_prime_pow {R S : Type*} [CommRing R] [Semiring S] (f : R →+* S)
    {p : ℕ} (k : ℕ) [Fact p.Prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p := by simp
#align polynomial.eval₂_one_cyclotomic_prime_pow Polynomial.eval₂_one_cyclotomic_prime_pow

private theorem cyclotomic_neg_one_pos {n : ℕ} (hn : 2 < n) {R} [LinearOrderedCommRing R] :
    0 < eval (-1 : R) (cyclotomic n R) := by
  haveI := NeZero.of_gt hn
  rw [← map_cyclotomic_int, ← Int.cast_one, ← Int.cast_neg, eval_int_cast_map, Int.coe_castRingHom,
    Int.cast_pos]
  suffices 0 < eval (↑(-1 : ℤ)) (cyclotomic n ℝ) by
    rw [← map_cyclotomic_int n ℝ, eval_int_cast_map, Int.coe_castRingHom] at this
    simpa only [Int.cast_pos] using this
  simp only [Int.cast_one, Int.cast_neg]
  have h0 := cyclotomic_coeff_zero ℝ hn.le
  rw [coeff_zero_eq_eval_zero] at h0
  by_contra! hx
  have := intermediate_value_univ (-1) 0 (cyclotomic n ℝ).continuous
  obtain ⟨y, hy : IsRoot _ y⟩ := this (show (0 : ℝ) ∈ Set.Icc _ _ by simpa [h0] using hx)
  rw [@isRoot_cyclotomic_iff] at hy
  rw [hy.eq_orderOf] at hn
  exact hn.not_le LinearOrderedRing.orderOf_le_two

theorem cyclotomic_pos {n : ℕ} (hn : 2 < n) {R} [LinearOrderedCommRing R] (x : R) :
    0 < eval x (cyclotomic n R) := by
  induction' n using Nat.strong_induction_on with n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x at this
  rw [← cons_self_properDivisors hn'.ne', Finset.erase_cons_of_ne _ hn''.ne', Finset.prod_cons,
    eval_mul, eval_geom_sum] at this
  rcases lt_trichotomy 0 (∑ i in Finset.range n, x ^ i) with (h | h | h)
  · apply pos_of_mul_pos_left
    · rwa [this]
    rw [eval_prod]
    refine' Finset.prod_nonneg fun i hi => _
    simp only [Finset.mem_erase, mem_properDivisors] at hi
    rw [geom_sum_pos_iff hn'.ne'] at h
    cases' h with hk hx
    · refine' (ih _ hi.2.2 (Nat.two_lt_of_ne _ hi.1 _)).le <;> rintro rfl
      · exact hn'.ne' (zero_dvd_iff.mp hi.2.1)
      · exact even_iff_not_odd.mp (even_iff_two_dvd.mpr hi.2.1) hk
    · rcases eq_or_ne i 2 with (rfl | hk)
      · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using hx.le
      refine' (ih _ hi.2.2 (Nat.two_lt_of_ne _ hi.1 hk)).le
      rintro rfl
      exact hn'.ne' <| zero_dvd_iff.mp hi.2.1
  · rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn'.ne'] at h
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn
  · apply pos_of_mul_neg_left
    · rwa [this]
    rw [geom_sum_neg_iff hn'.ne'] at h
    have h2 : 2 ∈ n.properDivisors.erase 1 := by
      rw [Finset.mem_erase, mem_properDivisors]
      exact ⟨by decide, even_iff_two_dvd.mp h.1, hn⟩
    rw [eval_prod, ← Finset.prod_erase_mul _ _ h2]
    apply mul_nonpos_of_nonneg_of_nonpos
    · refine' Finset.prod_nonneg fun i hi => le_of_lt _
      simp only [Finset.mem_erase, mem_properDivisors] at hi
      refine' ih _ hi.2.2.2 (Nat.two_lt_of_ne _ hi.2.1 hi.1)
      rintro rfl
      rw [zero_dvd_iff] at hi
      exact hn'.ne' hi.2.2.1
    · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using h.right.le
#align polynomial.cyclotomic_pos Polynomial.cyclotomic_pos

theorem cyclotomic_pos_and_nonneg (n : ℕ) {R} [LinearOrderedCommRing R] (x : R) :
    (1 < x → 0 < eval x (cyclotomic n R)) ∧ (1 ≤ x → 0 ≤ eval x (cyclotomic n R)) := by
  rcases n with (_ | _ | _ | n) <;>
    simp [cyclotomic_zero, cyclotomic_one, cyclotomic_two, succ_eq_add_one, eval_X, eval_one,
      eval_add, eval_sub, sub_nonneg, sub_pos, zero_lt_one, zero_le_one, imp_true_iff, imp_self,
      and_self_iff]
  · constructor <;> intro <;> norm_num <;> linarith
  · have : 2 < n + 3 := by linarith
    constructor <;> intro <;> [skip; apply le_of_lt] <;> apply cyclotomic_pos this
#align polynomial.cyclotomic_pos_and_nonneg Polynomial.cyclotomic_pos_and_nonneg

/-- Cyclotomic polynomials are always positive on inputs larger than one.
Similar to `cyclotomic_pos` but with the condition on the input rather than index of the
cyclotomic polynomial. -/
theorem cyclotomic_pos' (n : ℕ) {R} [LinearOrderedCommRing R] {x : R} (hx : 1 < x) :
    0 < eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).1 hx
#align polynomial.cyclotomic_pos' Polynomial.cyclotomic_pos'

/-- Cyclotomic polynomials are always nonnegative on inputs one or more. -/
theorem cyclotomic_nonneg (n : ℕ) {R} [LinearOrderedCommRing R] {x : R} (hx : 1 ≤ x) :
    0 ≤ eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).2 hx
#align polynomial.cyclotomic_nonneg Polynomial.cyclotomic_nonneg

theorem eval_one_cyclotomic_not_prime_pow {R : Type*} [Ring R] {n : ℕ}
    (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n) : eval 1 (cyclotomic n R) = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  rsuffices h | h : eval 1 (cyclotomic n ℤ) = 1 ∨ eval 1 (cyclotomic n ℤ) = -1
  · have := eval_int_cast_map (Int.castRingHom R) (cyclotomic n ℤ) 1
    simpa only [map_cyclotomic, Int.cast_one, h, eq_intCast] using this
  · exfalso
    linarith [cyclotomic_nonneg n (le_refl (1 : ℤ))]
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpe
  haveI := Fact.mk hp
  have := prod_cyclotomic_eq_geom_sum hn' ℤ
  apply_fun eval 1 at this
  rw [eval_geom_sum, one_geom_sum, eval_prod, eq_comm, ←
    Finset.prod_sdiff <| @range_pow_padicValNat_subset_divisors' p _ _, Finset.prod_image] at this
  simp_rw [eval_one_cyclotomic_prime_pow, Finset.prod_const, Finset.card_range, mul_comm] at this
  rw [← Finset.prod_sdiff <| show {n} ⊆ _ from _] at this
  swap
  · simp only [singleton_subset_iff, mem_sdiff, mem_erase, Ne.def, mem_divisors, dvd_refl,
      true_and_iff, mem_image, mem_range, exists_prop, not_exists, not_and]
    exact ⟨⟨hn.ne', hn'.ne'⟩, fun t _ => h hp _⟩
  rw [← Int.natAbs_ofNat p, Int.natAbs_dvd_natAbs] at hpe
  obtain ⟨t, ht⟩ := hpe
  rw [Finset.prod_singleton, ht, mul_left_comm, mul_comm, ← mul_assoc, mul_assoc] at this
  have : (p : ℤ) ^ padicValNat p n * p ∣ n := ⟨_, this⟩
  simp only [← _root_.pow_succ', ← Int.natAbs_dvd_natAbs, Int.natAbs_ofNat, Int.natAbs_pow] at this
  exact pow_succ_padicValNat_not_dvd hn'.ne' this
  · rintro x - y - hxy
    apply Nat.succ_injective
    exact Nat.pow_right_injective hp.two_le hxy
#align polynomial.eval_one_cyclotomic_not_prime_pow Polynomial.eval_one_cyclotomic_not_prime_pow

theorem sub_one_pow_totient_lt_cyclotomic_eval {n : ℕ} {q : ℝ} (hn' : 2 ≤ n) (hq' : 1 < q) :
    (q - 1) ^ totient n < (cyclotomic n ℝ).eval q := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀ ζ' ∈ primitiveRoots n ℂ, q - 1 ≤ ‖↑q - ζ'‖ := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, q - 1 < ‖↑q - ζ'‖ := by
    refine' ⟨ζ, (mem_primitiveRoots hn).mpr hζ, _⟩
    suffices ¬SameRay ℝ (q : ℂ) ζ by
      convert lt_norm_sub_of_not_sameRay this <;>
        simp only [hζ.norm'_eq_one hn.ne', Real.norm_of_nonneg hq.le, Complex.norm_real]
    rw [Complex.sameRay_iff]
    push_neg
    refine' ⟨mod_cast hq.ne', hζ.ne_zero hn.ne', _⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le, Ne.def, eq_comm, hζ.arg_eq_zero_iff hn.ne']
    clear_value ζ
    rintro rfl
    linarith [hζ.unique IsPrimitiveRoot.one]
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ)]
    simpa only [Complex.coe_algebraMap, Complex.ofReal_eq_zero] using (cyclotomic_pos' n hq').ne'
  suffices Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq']) ^ totient n <
      Units.mk0 ‖(cyclotomic n ℂ).eval ↑q‖₊ (by simp [this]) by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      hq'.le, Real.toNNReal_lt_toNNReal_iff_of_nonneg, coe_nnnorm, Complex.norm_eq_abs,
      NNReal.coe_pow, Real.coe_toNNReal', max_eq_left, sub_nonneg] at this
    convert this
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ), eq_comm]
    simp only [cyclotomic_nonneg n hq'.le, Complex.coe_algebraMap, Complex.abs_ofReal, abs_eq_self]
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq'])
  · simp only [Complex.card_primitiveRoots, prod_const, card_attach]
  · simp only [Subtype.coe_mk, Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, Complex.abs.nonneg, hq'.le, Units.val_mk0,
      Real.coe_toNNReal', coe_nnnorm, Complex.norm_eq_abs, max_le_iff, tsub_le_iff_right]
    intro x hx
    simpa only [and_true_iff, tsub_le_iff_right] using hfor x hx
  · simp only [Subtype.coe_mk, Finset.mem_attach, exists_true_left, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    simpa [hq'.le, Real.coe_toNNReal', max_eq_left, sub_nonneg] using hex
#align polynomial.sub_one_pow_totient_lt_cyclotomic_eval Polynomial.sub_one_pow_totient_lt_cyclotomic_eval

theorem sub_one_pow_totient_le_cyclotomic_eval {q : ℝ} (hq' : 1 < q) :
    ∀ n, (q - 1) ^ totient n ≤ (cyclotomic n ℝ).eval q
  | 0 => by simp only [totient_zero, _root_.pow_zero, cyclotomic_zero, eval_one, le_refl]
  | 1 => by simp only [totient_one, pow_one, cyclotomic_one, eval_sub, eval_X, eval_one, le_refl]
  | n + 2 => (sub_one_pow_totient_lt_cyclotomic_eval le_add_self hq').le
#align polynomial.sub_one_pow_totient_le_cyclotomic_eval Polynomial.sub_one_pow_totient_le_cyclotomic_eval

theorem cyclotomic_eval_lt_add_one_pow_totient {n : ℕ} {q : ℝ} (hn' : 3 ≤ n) (hq' : 1 < q) :
    (cyclotomic n ℝ).eval q < (q + 1) ^ totient n := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀ ζ' ∈ primitiveRoots n ℂ, ‖↑q - ζ'‖ ≤ q + 1 := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans_lt hq').le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, ‖↑q - ζ'‖ < q + 1 := by
    refine' ⟨ζ, (mem_primitiveRoots hn).mpr hζ, _⟩
    suffices ¬SameRay ℝ (q : ℂ) (-ζ) by
      convert norm_add_lt_of_not_sameRay this using 2
      · rw [Complex.norm_eq_abs, Complex.abs_ofReal]
        symm
        exact abs_eq_self.mpr hq.le
      · simp [abs_of_pos hq, hζ.norm'_eq_one hn.ne', -Complex.norm_eq_abs]
    rw [Complex.sameRay_iff]
    push_neg
    refine' ⟨mod_cast hq.ne', neg_ne_zero.mpr <| hζ.ne_zero hn.ne', _⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le, Ne.def, eq_comm]
    intro h
    rw [Complex.arg_eq_zero_iff, Complex.neg_re, neg_nonneg, Complex.neg_im, neg_eq_zero] at h
    have hζ₀ : ζ ≠ 0 := by
      clear_value ζ
      rintro rfl
      exact hn.ne' (hζ.unique IsPrimitiveRoot.zero)
    have : ζ.re < 0 ∧ ζ.im = 0 := ⟨h.1.lt_of_ne ?_, h.2⟩
    rw [← Complex.arg_eq_pi_iff, hζ.arg_eq_pi_iff hn.ne'] at this
    rw [this] at hζ
    linarith [hζ.unique <| IsPrimitiveRoot.neg_one 0 two_ne_zero.symm]
    · contrapose! hζ₀
      ext <;> simp [hζ₀, h.2]
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by
    erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ)]
    simp only [Complex.coe_algebraMap, Complex.ofReal_eq_zero]
    exact (cyclotomic_pos' n hq').ne.symm
  suffices Units.mk0 ‖(cyclotomic n ℂ).eval ↑q‖₊ (by simp [this]) <
      Units.mk0 (Real.toNNReal (q + 1)) (by simp; linarith) ^ totient n by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      hq'.le, Real.toNNReal_lt_toNNReal_iff_of_nonneg, coe_nnnorm, Complex.norm_eq_abs,
      NNReal.coe_pow, Real.coe_toNNReal', max_eq_left, sub_nonneg] at this
    convert this using 2
    · erw [cyclotomic.eval_apply q n (algebraMap ℝ ℂ), eq_comm]
      simp [cyclotomic_nonneg n hq'.le]
    rw [eq_comm, max_eq_left_iff]
    linarith
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q + 1)) (by simp; linarith only [hq'])
  · simp [Complex.card_primitiveRoots]
  · simp only [Subtype.coe_mk, Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, Complex.abs.nonneg, hq'.le, Units.val_mk0,
      Real.coe_toNNReal, coe_nnnorm, Complex.norm_eq_abs, max_le_iff]
    intro x hx
    have : Complex.abs _ ≤ _ := hfor x hx
    simp [this]
  · simp only [Subtype.coe_mk, Finset.mem_attach, exists_true_left, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    obtain ⟨ζ, hζ, hhζ : Complex.abs _ < _⟩ := hex
    exact ⟨ζ, hζ, by simp [hhζ]⟩
#align polynomial.cyclotomic_eval_lt_add_one_pow_totient Polynomial.cyclotomic_eval_lt_add_one_pow_totient

theorem cyclotomic_eval_le_add_one_pow_totient {q : ℝ} (hq' : 1 < q) :
    ∀ n, (cyclotomic n ℝ).eval q ≤ (q + 1) ^ totient n
  | 0 => by simp
  | 1 => by simp [add_assoc, add_nonneg, zero_le_one]
  | 2 => by simp
  | n + 3 => (cyclotomic_eval_lt_add_one_pow_totient le_add_self hq').le
#align polynomial.cyclotomic_eval_le_add_one_pow_totient Polynomial.cyclotomic_eval_le_add_one_pow_totient

theorem sub_one_pow_totient_lt_natAbs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq : q ≠ 1) :
    (q - 1) ^ totient n < ((cyclotomic n ℤ).eval ↑q).natAbs := by
  rcases hq.lt_or_lt.imp_left Nat.lt_one_iff.mp with (rfl | hq')
  · rw [zero_tsub, zero_pow (Nat.totient_pos (pos_of_gt hn')), pos_iff_ne_zero, Int.natAbs_ne_zero,
      Nat.cast_zero, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn']
    exact one_ne_zero
  rw [← @Nat.cast_lt ℝ, Nat.cast_pow, Nat.cast_sub hq'.le, Nat.cast_one, Int.cast_natAbs]
  refine' (sub_one_pow_totient_lt_cyclotomic_eval hn' (Nat.one_lt_cast.2 hq')).trans_le _
  convert (cyclotomic.eval_apply (q : ℤ) n (algebraMap ℤ ℝ)).trans_le (le_abs_self _)
  simp
#align polynomial.sub_one_pow_totient_lt_nat_abs_cyclotomic_eval Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval

theorem sub_one_lt_natAbs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq : q ≠ 1) :
    q - 1 < ((cyclotomic n ℤ).eval ↑q).natAbs :=
  calc
    q - 1 ≤ (q - 1) ^ totient n := Nat.le_self_pow (Nat.totient_pos <| pos_of_gt hn').ne' _
    _ < ((cyclotomic n ℤ).eval ↑q).natAbs := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hq
#align polynomial.sub_one_lt_nat_abs_cyclotomic_eval Polynomial.sub_one_lt_natAbs_cyclotomic_eval

end Polynomial
