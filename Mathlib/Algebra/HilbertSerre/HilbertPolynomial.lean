/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.HilbertSerre.Theorem

/-!
# Hilbert Polynomial

-/

universe u
variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable [noetherian_ring : IsNoetherianRing A] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜) (hS : ∀ (i : S.toFinset), S.deg i.2 = 1)

open GradedRing.finite_algebra_over_degree_zero_subring
open GradedModule.finite_module_over_degree_zero_subring
open CategoryTheory.Limits
open BigOperators
open PowerSeries


namespace PowerSeries

variable {R : Type _} [CommRing R]

theorem one_sub_inv_mul_eq_one : (1 - X : PowerSeries R) * (mk fun _ => 1) = 1 := by
  rw [PowerSeries.ext_iff]; exact λ n ↦ by
    by_cases hn : n = 0
    · subst hn; simp only [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one,
      constantCoeff_X, sub_zero, one_mul, coeff_one, ↓reduceIte]; rfl
    · rw [sub_mul]; simp only [one_mul, map_sub, coeff_mk, coeff_one, hn, ↓reduceIte];
      rw [show n = (n - 1) + 1 by exact (Nat.succ_pred hn).symm, PowerSeries.coeff_succ_X_mul];
      simp only [coeff_mk, sub_self]

/-- `1 - X`. -/
noncomputable def oneSub : (PowerSeries R)ˣ where
  val := 1 - X
  inv := mk fun _ => 1
  val_inv := one_sub_inv_mul_eq_one
  inv_val := by
    rw [mul_comm]; exact one_sub_inv_mul_eq_one

/-- `mk fun _ => 1`. -/
noncomputable def invOneSub : (PowerSeries R)ˣ where
  val := mk fun _ => 1
  inv := 1 - X
  val_inv := by
    rw [mul_comm]; exact one_sub_inv_mul_eq_one
  inv_val := one_sub_inv_mul_eq_one

theorem oneSub_inv_eq_invOneSub : (oneSub⁻¹ : (PowerSeries R)ˣ) = invOneSub := rfl

/-- `(1 - X) ^ (d + 1)`. -/
noncomputable def oneSubPow (d : ℕ) : (PowerSeries R)ˣ where
  val := (1 - X) ^ (d + 1)
  inv := PowerSeries.invOfUnit ((1 - X) ^ (d + 1)) 1
  val_inv := @PowerSeries.mul_invOfUnit R _ ((1 - X) ^ (d + 1)) 1 <|
    show (constantCoeff R) ((1 - X) ^ (d + 1)) = 1 by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp only [coeff_zero_eq_constantCoeff, map_pow,
    map_sub, map_one, constantCoeff_X, sub_zero, one_pow]
  inv_val := by
    rw [mul_comm]
    exact @PowerSeries.mul_invOfUnit R _ ((1 - X) ^ (d + 1)) 1 <|
      show (constantCoeff R) ((1 - X) ^ (d + 1)) = 1 by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp only [coeff_zero_eq_constantCoeff, map_pow,
      map_sub, map_one, constantCoeff_X, sub_zero, one_pow]

theorem oneSubPow_eq_oneSub_pow (d : ℕ) :
    oneSubPow d = (oneSub ^ (d + 1) : (PowerSeries R)ˣ) := Units.eq_iff.mp rfl

/-- `mk fun n => Nat.choose (d + n) d`. -/
noncomputable def invOneSubPow' (d : ℕ) : (PowerSeries R)ˣ where
  val := mk fun n => Nat.choose (d + n) d
  inv := PowerSeries.invOfUnit (mk fun n => Nat.choose (d + n) d) 1
  val_inv := @PowerSeries.mul_invOfUnit R _ (mk fun n => Nat.choose (d + n) d) 1 <| show
    (constantCoeff R) (mk fun n => Nat.choose (d + n) d) = 1 by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [coeff_mk, add_zero, Nat.choose_self, Nat.cast_one]
  inv_val := by
    rw [mul_comm]
    exact @PowerSeries.mul_invOfUnit R _ (mk fun n => Nat.choose (d + n) d) 1 <| show
    (constantCoeff R) (mk fun n => Nat.choose (d + n) d) = 1 by
      rw [← coeff_zero_eq_constantCoeff_apply]
      simp only [coeff_mk, add_zero, Nat.choose_self, Nat.cast_one]

lemma invOneSub_pow_eq_invOneSubPow' (d : ℕ) :
    invOneSub ^ (d + 1) = (invOneSubPow' d : (PowerSeries R)ˣ) := by
  rw [invOneSub, invOneSubPow']
  have : (@mk R fun _ ↦ 1) ^ (d + 1) = @mk R fun n ↦ (Nat.choose (d + n) d) := by
    induction' d with d hd
    · simp only [Nat.zero_eq, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one]
    · ring_nf
      rw [show Nat.succ d = d + 1 by rfl, PowerSeries.ext_iff]
      exact λ n ↦ by
        rw [hd, coeff_mul]; simp only [coeff_mk, one_mul]; rw [Nat.succ_add,
        Nat.choose_succ_succ, ←Finset.sum_antidiagonal_choose_add]; exact (Nat.cast_sum
        (Finset.antidiagonal n) fun x ↦ Nat.choose (d + x.2) d).symm
  exact Units.eq_iff.mp this

theorem oneSub_inv_pow_eq_invOneSubPow' (d : ℕ) :
    oneSub⁻¹ ^ (d + 1) = (invOneSubPow' d : (PowerSeries R)ˣ) := by
  rw [oneSub_inv_eq_invOneSub]; exact invOneSub_pow_eq_invOneSubPow' d

theorem oneSub_inv_pow_eq_oneSub_pow_inv (d : ℕ) :
    oneSub⁻¹ ^ (d + 1) = (oneSubPow d : (PowerSeries R)ˣ)⁻¹ := by
  induction' d with d hd
  · simp only [Nat.zero_eq, zero_add, pow_one, inv_inj]
    exact Units.eq_iff.mp <| show (1 - X : PowerSeries R) = (1 - X) ^ 1 by simp only [pow_one]
  · erw [pow_succ, hd, ← mul_inv, inv_inj]
    exact Units.eq_iff.mp <| show (1 - X) * ((1 - X) ^ (d + 1)) = (1 - X) ^ (d + 1 + 1) by rfl

theorem oneSubPow_inv_eq_invOneSubPow' (d : ℕ) :
    (oneSubPow d : (PowerSeries R)ˣ)⁻¹ = invOneSubPow' d := by
  rw [← oneSub_inv_pow_eq_oneSub_pow_inv]; exact oneSub_inv_pow_eq_invOneSubPow' d

end PowerSeries

namespace Hilbert

open PowerSeries

/--
Look at the theorem `prePolynomial_eq_choose`, which states that for any `n : Set.Ici N`,
`Polynomial.eval (n : ℚ) (prePolynomial N d k) = Nat.choose (n - k + d) d`.
-/
noncomputable def prePolynomial (N : ℕ) (d : ℕ) (k : Fin (N + 1)) :
    Polynomial ℚ := (d.factorial : ℚ)⁻¹ •
  (∏ i : Finset.range d, (Polynomial.X - (Polynomial.C (k : ℚ)) + (Polynomial.C (i : ℚ)) + 1))

/-- Cost a lot of work, but later proved to be useless. -/
theorem prePolynomial_eq_choose_of_k_eq_zero (N : ℕ) (d : ℕ) (n : Set.Ici N) :
    Polynomial.eval (n : ℚ) (prePolynomial N d ⟨0, by simp only
    [add_pos_iff, zero_lt_one, or_true]⟩) = Nat.choose (n + d) d := by
  rw [prePolynomial]; simp only [Finset.univ_eq_attach, CharP.cast_eq_zero, map_zero, sub_zero,
  map_natCast, Polynomial.eval_smul, smul_eq_mul]
  induction' d with d hd
  · simp only [Nat.zero_eq, Nat.factorial_zero, Nat.cast_one, inv_one, Finset.range_zero,
      Finset.attach_empty, Finset.prod_empty, Polynomial.eval_one, mul_one, add_zero,
      Nat.choose_zero_right]
  · rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, @Finset.prod_attach (Polynomial ℚ) ℕ _
      (Finset.range (Nat.succ d)) (fun x => Polynomial.X + (@Nat.cast (Polynomial ℚ)
      NonAssocSemiring.toNatCast ↑x) + 1), Finset.prod_range_succ]
    rw [@Finset.prod_attach (Polynomial ℚ) ℕ _ (Finset.range d) (fun x => Polynomial.X +
      (@Nat.cast (Polynomial ℚ) NonAssocSemiring.toNatCast ↑x) + 1)] at hd
    rw [mul_assoc, Polynomial.eval_mul]
    rw [← mul_assoc (@Nat.cast ℚ NonAssocSemiring.toNatCast (Nat.factorial d))⁻¹, hd]
    simp only [Nat.cast_add, Nat.cast_one, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_nat_cast, Polynomial.eval_one]
    rw [Nat.add_succ, show (↑d + 1)⁻¹ = Ring.inverse ((d : ℚ) + 1) by simp only
      [Ring.inverse_eq_inv'], Ring.inverse_mul_eq_iff_eq_mul, ← Nat.cast_add, ← Nat.cast_add_one,
      ← Nat.cast_mul, ← Nat.cast_add_one, ← Nat.cast_mul, show (Nat.choose ((n : ℕ) + d) d) *
      ((n : ℕ) + d + 1) = (d + 1) * (Nat.choose (Nat.succ (n : ℕ) + d)) (Nat.succ d) by rw
      [mul_comm, Nat.succ_mul_choose_eq, Nat.succ_add, mul_comm], Nat.succ_add]
    exact Ne.isUnit <| show (d : ℚ) + 1 ≠ 0 by exact Nat.cast_add_one_ne_zero d

theorem prePolynomial_eq_choose (N : ℕ) (d : ℕ) (k : Fin (N + 1)) (n : Set.Ici N) :
    Polynomial.eval (n : ℚ) (prePolynomial N d k) = Nat.choose (n - k + d) d := by
  rw [prePolynomial]
  simp only [Finset.univ_eq_attach, map_natCast, Polynomial.eval_smul, smul_eq_mul]
  rw [Polynomial.eval_prod, @Finset.prod_attach ℚ ℕ _ (Finset.range d) (fun j =>
    Polynomial.eval (↑↑n) (Polynomial.X - (@Nat.cast (Polynomial ℚ) NonAssocSemiring.toNatCast ↑k)
    + (@Nat.cast (Polynomial ℚ) NonAssocSemiring.toNatCast ↑j) + 1))]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_nat_cast,
    Polynomial.eval_one]
  rw [Nat.add_choose, Nat.cast_div, Nat.cast_mul, div_mul_eq_div_div, mul_comm, div_eq_mul_inv]
  simp only [mul_eq_mul_right_iff, _root_.inv_eq_zero, Nat.cast_eq_zero]
  · left; rw [← Nat.cast_div, ← Nat.ascFactorial_eq_div]
    induction' d with d hd
    · simp only [Nat.zero_eq, Finset.range_zero, Finset.prod_empty, Nat.ascFactorial_zero,
        Nat.cast_one]
    · rw [Finset.prod_range_succ, hd, add_assoc, add_comm (@Nat.cast ℚ Semiring.toNatCast d) 1,
        ← add_assoc, mul_comm, ← Nat.cast_sub, ← Nat.cast_add_one, ← Nat.cast_add, ← Nat.cast_mul,
        ← Nat.ascFactorial_succ]
      exact le_trans (Fin.is_le k) n.2
    · exact Nat.factorial_dvd_factorial <| Nat.le_add_right (↑n - ↑k) d
    · simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero (↑n - ↑k)
  · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _
  · exact λ h ↦ by
      rw [Nat.cast_mul, mul_eq_zero] at h; exact Or.elim h (by
      simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero (↑n - ↑k)) (by
      simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero d)

/--
Look at `polynomial_smul_invOneSubPow'_coeff_eq_polynomial_of_polynomial_eval`,
which says that `(PowerSeries.coeff ℤ n) (p * (@invOneSubPow' ℤ _ d))` is equal to
`Polynomial.eval (n : ℚ) (polynomial_of_polynomial p d)` for any `n` belonging to
`Set.Ici (Polynomial.natDegree p)`.
-/
noncomputable def polynomial_of_polynomial (p : Polynomial ℤ) (d : ℕ) : Polynomial ℚ :=
  ∑ i in Finset.range (Polynomial.natDegree p + 1),
  (Polynomial.coeff p i) • prePolynomial (Polynomial.natDegree p) d i

theorem polynomial_mul_invOneSubPow'_coeff_eq_polynomial_of_polynomial_eval
    (p : Polynomial ℤ) (d : ℕ) (n : Set.Ici (Polynomial.natDegree p)) :
    (PowerSeries.coeff ℤ n) (p * (@invOneSubPow' ℤ _ d)) =
    Polynomial.eval (n : ℚ) (polynomial_of_polynomial p d) := by
  rw [show @Polynomial.ToPowerSeries ℤ Int.instCommSemiringInt p = @Polynomial.ToPowerSeries
    ℤ Int.instCommSemiringInt (Finset.sum (Finset.range (Polynomial.natDegree p + 1))
    (fun (i : ℕ) => ((Polynomial.coeff p i) • (Polynomial.X ^ i)))) by
    simp only [zsmul_eq_mul, Polynomial.coe_inj]; exact Polynomial.as_sum_range_C_mul_X_pow p,
    invOneSubPow', polynomial_of_polynomial]
  simp only [zsmul_eq_mul]
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_int_cast]
  simp_rw [prePolynomial_eq_choose]
  rw [PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe, Polynomial.finset_sum_coeff, Polynomial.coeff_intCast_mul,
    Int.cast_id, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range, coeff_mk, ite_mul, zero_mul, Int.cast_sum, Int.cast_ite, Int.cast_mul,
    Int.cast_ofNat, Int.cast_zero, Fin.val_nat_cast]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show Nat.succ (@Subtype.val ℕ (fun x ↦ x
    ∈ Set.Ici (Polynomial.natDegree p)) n) = (Polynomial.natDegree p + 1) + (Nat.succ (@Subtype.val
    ℕ (fun x ↦ x ∈ Set.Ici (Polynomial.natDegree p)) n) - (Polynomial.natDegree p + 1)) by
    simp only [Nat.succ_sub_succ_eq_sub]; rw [add_assoc, add_comm, add_assoc, Nat.sub_add_cancel];
    exact Nat.succ_eq_one_add ↑n; exact n.2, Finset.sum_range_add]
  simp only [Nat.succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_sum_iff_of_le]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [show (if i < Polynomial.natDegree p + 1 then (@Int.cast ℚ NonAssocRing.toIntCast
      (Polynomial.coeff p i)) * (@Nat.cast ℚ AddMonoidWithOne.toNatCast (Nat.choose (d + (↑n - i))
      d)) else 0) = ↑(Polynomial.coeff p i) * ↑(Nat.choose (d + (↑n - i)) d) by simp only [hi,
      ↓reduceIte]]
    simp only [mul_eq_mul_left_iff, Nat.cast_inj, Int.cast_eq_zero]
    rw [Nat.mod_eq_of_lt, add_comm]
    exact Or.inl rfl
    exact hi
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [show (if i < Polynomial.natDegree p + 1 then (@Int.cast ℚ NonAssocRing.toIntCast
      (Polynomial.coeff p i)) * (@Nat.cast ℚ AddMonoidWithOne.toNatCast (Nat.choose (d + (↑n - i))
      d)) else 0) = ↑(Polynomial.coeff p i) * ↑(Nat.choose (d + (↑n - i)) d) by simp only [hi,
      ↓reduceIte]]
    rw [Nat.mod_eq_of_lt, add_comm]
    exact hi

end Hilbert

namespace generatingSetOverBaseRing

open PowerSeries

lemma poles_eq_one_sub_pow_of_deg_eq_one : (poles S : ℤ⟦X⟧) = (1 - X) ^ S.toFinset.card := by
  simp only [val_poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach]

lemma poles_eq_oneSubPow_of_deg_eq_one_and_card_gt_zero (hS' : S.toFinset.card > 0) :
    (poles S : ℤ⟦X⟧) = (oneSubPow (S.toFinset.card - 1)).val := by
  rw [poles_eq_one_sub_pow_of_deg_eq_one, oneSubPow]; simp only;
  rw [instHAdd, instAddNat, Nat.sub_add_cancel hS']; exact hS

lemma poles_eq_oneSubPow_of_deg_eq_one_and_card_gt_zero' (hS' : S.toFinset.card > 0) :
    poles S = oneSubPow (S.toFinset.card - 1) :=
  Units.eq_iff.mp <| poles_eq_oneSubPow_of_deg_eq_one_and_card_gt_zero 𝒜 S hS hS'

end generatingSetOverBaseRing

namespace HilbertSerre

open generatingSetOverBaseRing

lemma _root_.hilbert_serre' : ∃ (p : Polynomial ℤ), μ.poincareSeries 𝒜 ℳ = p * S.poles⁻¹ :=
  statement'_imp_statement 𝒜 ℳ μ S proof'.{u}

/--
An auxiliary polynomial that is helpful for defining the Hilbert polynomial.
-/
noncomputable def auxPolynomial : Polynomial ℤ := (hilbert_serre' 𝒜 ℳ μ S).choose

lemma auxPolynomial_mul_eq :
    (auxPolynomial 𝒜 ℳ μ S).ToPowerSeries * S.poles⁻¹ =
    μ.poincareSeries 𝒜 ℳ :=
  Eq.symm (hilbert_serre' 𝒜 ℳ μ S).choose_spec

/--
The Hilbert polynomial, i.e. the polynomial such that for any `n : ℕ` which
is big enough, its value at `n` is equal to `μ <| .of _ <| (ℳ n : Type u)`.
-/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  if S.toFinset.card = 0 then 0
  else Hilbert.polynomial_of_polynomial
  (auxPolynomial 𝒜 ℳ μ S) (S.toFinset.card - 1)

theorem additiveFunction_eq_hilbertPolynomial_eval
    (n : ℕ) (hn : (auxPolynomial 𝒜 ℳ μ S).natDegree < n) :
    (μ <| .of _ <| (ℳ n : Type u) : ℚ) =
    Polynomial.eval (n : ℚ) (hilbertPolynomial 𝒜 ℳ μ S) := by
  have hμ : μ (FGModuleCat.of ↥(𝒜 0) ↥(ℳ n)) = coeff ℤ n (μ.poincareSeries 𝒜 ℳ) := by
    rw [AdditiveFunction.poincareSeries]; simp only [coeff_mk]
  by_cases hS' : IsEmpty S.toFinset
  · rw [hilbertPolynomial]
    simp only [show S.toFinset.card = 0 by
      rw [Finset.card_eq_zero]; exact Finset.isEmpty_coe_sort.mp hS',
      ↓reduceIte, Polynomial.eval_zero, Int.cast_eq_zero]
    rw [hμ, ← auxPolynomial_mul_eq 𝒜 ℳ μ S, generatingSetOverBaseRing.poles]
    simp_rw [Finset.eq_empty_of_isEmpty (Finset.attach S.toFinset), Finset.prod_empty]
    simp only [Units.inv_mk]
    rw [show (invOfUnit 1 1 : PowerSeries ℤ) = 1 by
      rw [← one_mul (invOfUnit 1 1)]; exact mul_invOfUnit 1 1 rfl]
    simp only [mul_one, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hn
  · rw [hμ, ← auxPolynomial_mul_eq 𝒜 ℳ μ S, hilbertPolynomial]
    have hS1 : S.toFinset.card ≠ 0 := λ h ↦ hS' <| show IsEmpty S.toFinset by
      rw [Finset.card_eq_zero] at h; exact Finset.isEmpty_coe_sort.mpr h
    rw [if_neg hS1, poles_eq_oneSubPow_of_deg_eq_one_and_card_gt_zero',
      PowerSeries.oneSubPow_inv_eq_invOneSubPow']
    let m : Set.Ici (Polynomial.natDegree (auxPolynomial 𝒜 ℳ μ S)) :=
      ⟨n, Nat.lt_succ.mp (Nat.le.step hn)⟩
    rw [show @Nat.cast ℚ Semiring.toNatCast n = (m : ℚ) by
      simp only, ← Hilbert.polynomial_mul_invOneSubPow'_coeff_eq_polynomial_of_polynomial_eval]
    exact fun i ↦ hS i
    exact Nat.pos_of_ne_zero hS1

end HilbertSerre
