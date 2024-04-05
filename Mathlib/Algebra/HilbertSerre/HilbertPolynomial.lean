/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.PowerSeries.WellKnown
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


namespace Hilbert

open PowerSeries

/--
Look at the theorem `prePolynomial_eq_choose`, which states that for any `n : Set.Ici N`,
`Polynomial.eval (n : ℚ) (prePolynomial N d k) = Nat.choose (n - k + d) d`.
-/
noncomputable def prePolynomial (d : ℕ) (k : ℕ) :
    Polynomial ℚ := (d.factorial : ℚ)⁻¹ •
  (∏ i : Finset.range d, (Polynomial.X - (Polynomial.C (k : ℚ)) + (Polynomial.C (i : ℚ)) + 1))

theorem prePolynomial_eq_choose (d : ℕ) (k n : ℕ) (hkn : k ≤ n):
    Polynomial.eval (n : ℚ) (prePolynomial d k) = Nat.choose (n - k + d) d := by
  rw [prePolynomial]
  simp only [Finset.univ_eq_attach, map_natCast, Polynomial.eval_smul, smul_eq_mul]
  rw [Polynomial.eval_prod, @Finset.prod_attach ℚ ℕ _ (Finset.range d) (fun j => Polynomial.eval
    n (Polynomial.X - (@Nat.cast (Polynomial ℚ) NonAssocSemiring.toNatCast k) + (@Nat.cast
    (Polynomial ℚ) NonAssocSemiring.toNatCast j) + 1))]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_nat_cast,
    Polynomial.eval_one]
  rw [Nat.add_choose, Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial_add _ _) (λ h ↦ by
    simp only [Nat.cast_mul, mul_eq_zero, Nat.cast_eq_zero] at h;
    exact Or.elim h (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)), Nat.cast_mul,
    div_mul_eq_div_div, mul_comm, div_eq_mul_inv]
  simp only [mul_eq_mul_right_iff, _root_.inv_eq_zero, Nat.cast_eq_zero]
  · left; rw [← Nat.cast_div (Nat.factorial_dvd_factorial <| Nat.le_add_right (n - k) d) (by
    simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero (n - k)),
      ← Nat.ascFactorial_eq_div]
    induction' d with d hd
    · simp only [Nat.zero_eq, Finset.range_zero, Finset.prod_empty, Nat.ascFactorial_zero,
        Nat.cast_one]
    · rw [Finset.prod_range_succ, hd, add_assoc, add_comm (@Nat.cast ℚ Semiring.toNatCast d),
        ← add_assoc, mul_comm, ← Nat.cast_sub hkn, ← Nat.cast_add_one, ← Nat.cast_add,
        ← Nat.cast_mul, ← Nat.ascFactorial_succ]

/--
Look at `polynomial_smul_invOneSubPow'_coeff_eq_polynomial_of_polynomial_eval`,
which says that `(PowerSeries.coeff ℤ n) (p * (@invOneSubPow' ℤ _ d))` is equal to
`Polynomial.eval (n : ℚ) (polynomial_of_polynomial p d)` for any `n` belonging to
`Set.Ici (Polynomial.natDegree p)`.
-/
noncomputable def polynomial_of_polynomial (p : Polynomial ℤ) (d : ℕ) : Polynomial ℚ :=
  ∑ i in Finset.range (Polynomial.natDegree p + 1), (Polynomial.coeff p i) • prePolynomial d i

theorem polynomial_mul_invOneSubPow''_coeff_eq_polynomial_of_polynomial_eval
    (p : Polynomial ℤ) (d : ℕ) (n : ℕ) (hn : Polynomial.natDegree p ≤ n) :
    (PowerSeries.coeff ℤ n) (p * (@invOneSubPow ℤ _ d)) =
    Polynomial.eval (n : ℚ) (polynomial_of_polynomial p d) := by
  rw [show p.ToPowerSeries = (Finset.sum (Finset.range (Polynomial.natDegree p + 1)) (fun (i : ℕ)
    => (Polynomial.coeff p i) • (Polynomial.X ^ i)) : Polynomial ℤ).ToPowerSeries by
    simp only [zsmul_eq_mul, Polynomial.coe_inj]; exact Polynomial.as_sum_range_C_mul_X_pow p,
    invOneSubPow, polynomial_of_polynomial]
  simp only [zsmul_eq_mul]; rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_int_cast]
  rw [(Finset.sum_eq_sum_iff_of_le (λ i hi ↦ by
    simp only [Subtype.forall, Finset.mem_range] at *; rw [prePolynomial_eq_choose d i n <|
    Nat.le_trans (Nat.le_of_lt_succ hi) hn])).2 <| λ i hi ↦ by
    simp only [Subtype.forall, Finset.mem_range, mul_eq_mul_left_iff, Int.cast_eq_zero] at *;
    exact Or.intro_left _ <| prePolynomial_eq_choose d i n <|
    Nat.le_trans (Nat.le_of_lt_succ hi) hn, PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe, Polynomial.finset_sum_coeff, Polynomial.coeff_intCast_mul,
    Int.cast_id, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range, coeff_mk, ite_mul, zero_mul, Int.cast_sum, Int.cast_ite, Int.cast_mul,
    Int.cast_ofNat, Int.cast_zero]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show Nat.succ n =
    (Polynomial.natDegree p + 1) + ((Nat.succ n) - (Polynomial.natDegree p + 1)) by
    simp only [Nat.succ_sub_succ_eq_sub]; rw [add_assoc, add_comm, add_assoc,
    Nat.sub_add_cancel hn]; exact Nat.succ_eq_one_add n, Finset.sum_range_add]
  simp only [Nat.succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', ↓reduceIte,
    Finset.sum_const_zero, add_zero]
  exact (Finset.sum_eq_sum_iff_of_le <| λ i hi ↦ by
    simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte, mul_eq_mul_left_iff,
    Nat.cast_inj, Int.cast_eq_zero]; rw [add_comm]).2 <| λ i hi ↦ by
    simp only [Finset.mem_range] at hi; simp only [hi, ↓reduceIte]; rw [add_comm]

end Hilbert

namespace generatingSetOverBaseRing

open PowerSeries

lemma poles_eq_one_sub_pow_of_deg_eq_one : poles S =
    ⟨1 - X, invOfUnit (1 - X) 1, mul_invOfUnit (1 - X) 1 <| by
    simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
    rw [mul_comm]; exact mul_invOfUnit (1 - X) 1 <| by simp only [map_sub, map_one,
    constantCoeff_X, sub_zero, Units.val_one]⟩ ^ S.toFinset.card := by
  rw [poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach]
  exact Units.eq_iff.mp rfl

end generatingSetOverBaseRing

namespace HilbertSerre

open Polynomial
open generatingSetOverBaseRing
open Hilbert

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
Assume that `auxPolynomial 𝒜 ℳ μ S ≠ 0`. The greatest factor of `auxPolynomial 𝒜 ℳ μ S`
that does not have the factor `1 - X`.
-/
noncomputable def auxPolynomial' (hn0 : auxPolynomial 𝒜 ℳ μ S ≠ 0) : Polynomial ℤ :=
  ((- 1) ^ (Polynomial.rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S))) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (auxPolynomial 𝒜 ℳ μ S) hn0 1).choose

theorem pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial
    (hn0 : auxPolynomial 𝒜 ℳ μ S ≠ 0) :
    ((1 - Polynomial.X) ^ (Polynomial.rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S))) *
    (auxPolynomial' 𝒜 ℳ μ S hn0) = auxPolynomial 𝒜 ℳ μ S := by
  rw [auxPolynomial', ← mul_assoc, ← mul_pow]; simp only [mul_neg, mul_one, neg_sub, map_one];
  exact id (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (auxPolynomial 𝒜 ℳ μ S)
    hn0 1).choose_spec.1.symm

theorem auxPolynomial'_ne_zero (h : auxPolynomial 𝒜 ℳ μ S ≠ 0) :
    auxPolynomial' 𝒜 ℳ μ S h ≠ 0 := λ h0 ↦ by
  let hpow := pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial 𝒜 ℳ μ S h
  rw [h0] at hpow; simp at hpow; exact h (id hpow.symm)

theorem natDegree_auxPolynomial'_le (h : auxPolynomial 𝒜 ℳ μ S ≠ 0) :
    (auxPolynomial' 𝒜 ℳ μ S h).natDegree ≤ (auxPolynomial 𝒜 ℳ μ S).natDegree := by
  rw [← pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial 𝒜 ℳ μ S h]
  rw [Polynomial.natDegree_mul]
  exact Nat.le_add_left (natDegree (auxPolynomial' 𝒜 ℳ μ S h))
    (natDegree ((1 - Polynomial.X) ^ rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S)))
  exact pow_ne_zero _ <| λ h0 ↦ by
    let this : (@HSub.hSub ℤ[X] ℤ[X] ℤ[X] instHSub (OfNat.ofNat 1) X).coeff 0 = 0 := by
      rw [h0]; simp only [coeff_zero]
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  exact auxPolynomial'_ne_zero 𝒜 ℳ μ S h

theorem natDegree_pow_mul_auxPolynomial'_le (h : ¬auxPolynomial 𝒜 ℳ μ S = 0)
    (h1 : S.toFinset.card ≤ rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S)) :
    natDegree ((Polynomial.C 1 - Polynomial.X) ^ (rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) -
    S.toFinset.card) * auxPolynomial' 𝒜 ℳ μ S h) ≤ natDegree (auxPolynomial 𝒜 ℳ μ S) := by
  rw [show natDegree (auxPolynomial 𝒜 ℳ μ S) = natDegree (((1 - Polynomial.X)
    ^ (rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - S.toFinset.card
    + S.toFinset.card)) * (auxPolynomial' 𝒜 ℳ μ S h)) by
    rw [← Nat.eq_add_of_sub_eq h1 rfl, pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial],
    pow_add, mul_assoc, mul_comm ((1 - Polynomial.X) ^ S.toFinset.card), ← mul_assoc,
    natDegree_mul, natDegree_mul, natDegree_mul]
  simp only [map_one, natDegree_pow, le_add_iff_nonneg_right, zero_le]
  · exact pow_ne_zero _ <| λ h0 ↦ by
      let this : (@HSub.hSub ℤ[X] ℤ[X] ℤ[X] instHSub (OfNat.ofNat 1) X).coeff 0 = 0 := by
        rw [h0]; simp only [coeff_zero]
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact auxPolynomial'_ne_zero 𝒜 ℳ μ S h
  · rw [mul_ne_zero_iff]; exact ⟨pow_ne_zero _ <| λ h0 ↦ by
      let this : (@HSub.hSub ℤ[X] ℤ[X] ℤ[X] instHSub (OfNat.ofNat 1) X).coeff 0 = 0 := by
        rw [h0]; simp only [coeff_zero]
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this,
      auxPolynomial'_ne_zero 𝒜 ℳ μ S h⟩
  · exact pow_ne_zero _ <| λ h0 ↦ by
      let this : (@HSub.hSub ℤ[X] ℤ[X] ℤ[X] instHSub (OfNat.ofNat 1) X).coeff 0 = 0 := by
        rw [h0]; simp only [coeff_zero]
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact pow_ne_zero _ <| λ h0 ↦ by
      let this : (@HSub.hSub ℤ[X] ℤ[X] ℤ[X] instHSub (OfNat.ofNat 1) X).coeff 0 = 0 := by
        erw [h0]; simp only [coeff_zero]
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact auxPolynomial'_ne_zero 𝒜 ℳ μ S h

/--
The Hilbert polynomial, i.e. the polynomial such that for any `n : ℕ` which
is big enough, its value at `n` is equal to `μ <| .of _ <| (ℳ n : Type u)`.
-/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  if h : auxPolynomial 𝒜 ℳ μ S = 0 then 0
  else (if S.toFinset.card ≤ (auxPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 then 0
  else Hilbert.polynomial_of_polynomial
  (auxPolynomial' 𝒜 ℳ μ S h) (S.toFinset.card -
  ((auxPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) - 1))

theorem additiveFunction_val_eq_hilbertPolynomial_eval
    (n : ℕ) (hn : (auxPolynomial 𝒜 ℳ μ S).natDegree < n) :
    (μ <| .of _ <| (ℳ n : Type u) : ℚ) =
    Polynomial.eval (n : ℚ) (hilbertPolynomial 𝒜 ℳ μ S) := by
  have hμ : μ (FGModuleCat.of ↥(𝒜 0) ↥(ℳ n)) = coeff ℤ n (μ.poincareSeries 𝒜 ℳ) := by
    rw [AdditiveFunction.poincareSeries]; simp only [coeff_mk]
  by_cases h : auxPolynomial 𝒜 ℳ μ S = 0
  · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, eval_zero, Int.cast_eq_zero]
    rw [hμ, ← auxPolynomial_mul_eq 𝒜 ℳ μ S, h]; simp only [coe_zero, val_inv_poles, zero_mul]
    exact rfl
  · rw [hilbertPolynomial, hμ]; simp only [h, ↓reduceDite]
    let one_sub : ℤ⟦X⟧ˣ := ⟨1 - PowerSeries.X, invOfUnit (1 - PowerSeries.X) 1,
      @PowerSeries.mul_invOfUnit ℤ _ (1 - PowerSeries.X) 1 <| by
      simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
      rw [mul_comm]; exact @PowerSeries.mul_invOfUnit ℤ _ (1 - PowerSeries.X) 1 <| by
        simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one]⟩
    have one_sub_eq : 1 - PowerSeries.X = ((1 : ℤ[X]) - Polynomial.X).ToPowerSeries := by
      rw [PowerSeries.ext_iff]; exact λ i ↦ by_cases (λ (hi : i = 0) ↦ by
        simp only [hi, map_sub, PowerSeries.coeff_one, ↓reduceIte, coeff_zero_X, sub_zero, map_one,
        coeff_coe, coeff_sub, coeff_one_zero, coeff_X_zero]) (λ hi ↦ by
        simp only [map_sub, PowerSeries.coeff_one, hi, ↓reduceIte, zero_sub, map_one, coeff_coe,
        coeff_sub]; rw [Polynomial.coeff_one]; simp only [hi, ↓reduceIte, zero_sub, neg_inj];
        rw [Polynomial.coeff_X, PowerSeries.coeff_X]; exact by_cases (λ (hi : i = 1) ↦ by
        simp only [hi, ↓reduceIte]) (λ hi ↦ by
        simp only [hi, ↓reduceIte]; exact Eq.symm (if_neg (Ne.symm hi))))
    by_cases h1 : S.toFinset.card ≤ (auxPolynomial 𝒜 ℳ μ S).rootMultiplicity 1
    · simp only [h1, ↓reduceIte, eval_zero, Int.cast_eq_zero]
      rw [← auxPolynomial_mul_eq 𝒜 ℳ μ S,
        ← pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial 𝒜 ℳ μ S h,
        show poles S = one_sub ^ S.toFinset.card by
        rw [poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach];
        exact Units.eq_iff.mp rfl, coe_mul, coe_pow, show @ToPowerSeries ℤ
        Int.instCommSemiringInt (1 - Polynomial.X) = one_sub.val by
        simp only; rw [one_sub_eq], ← mul_comm, ← mul_assoc,
        ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_comm
        (one_sub ^ S.toFinset.card)⁻¹, ← pow_sub _ h1, Units.val_pow_eq_pow_val,
        show one_sub.val = ((@Polynomial.C ℤ _ 1) - Polynomial.X).ToPowerSeries by
        simp only [map_one]; rw [one_sub_eq], ← coe_pow, ← coe_mul, coeff_coe]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_mul_auxPolynomial'_le 𝒜 ℳ μ S h h1) hn)
    · simp only [h1, ↓reduceIte]
      rw [← auxPolynomial_mul_eq 𝒜 ℳ μ S, ← Polynomial.coe_inj.2 <|
        pow_rootMultiplicity_mul_auxPolynomial'_eq_auxPolynomial 𝒜 ℳ μ S h, coe_mul, coe_pow,
        ← one_sub_eq, show poles S = one_sub ^ S.toFinset.card by
        exact poles_eq_one_sub_pow_of_deg_eq_one 𝒜 S hS, mul_comm, ← mul_assoc,
        show (@HSub.hSub ℤ⟦X⟧ ℤ⟦X⟧ ℤ⟦X⟧ instHSub 1 PowerSeries.X) = one_sub by simp only,
        ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← inv_pow_sub one_sub <| Nat.le_of_not_ge h1]
      let m : Set.Ici (Polynomial.natDegree (auxPolynomial' 𝒜 ℳ μ S h)) := ⟨n, Nat.le_of_lt <|
        Nat.lt_of_le_of_lt (natDegree_auxPolynomial'_le 𝒜 ℳ μ S h) hn⟩
      rw [show @Nat.cast ℚ Semiring.toNatCast n = (m : ℚ) by simp only,
        ← polynomial_mul_invOneSubPow''_coeff_eq_polynomial_of_polynomial_eval _ _ _ (le_trans
        (natDegree_auxPolynomial'_le 𝒜 ℳ μ S h) <| Nat.lt_succ.mp (Nat.le.step hn)),
        show one_sub⁻¹ ^ (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S)) =
        invOneSubPow (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1) by
        rw [invOneSubPow_eq_inv_one_sub_pow, Nat.sub_add_cancel]; exact Nat.le_sub_of_add_le'
          (Nat.not_le.mp h1), mul_comm (auxPolynomial' 𝒜 ℳ μ S h).ToPowerSeries]

lemma coeff_S_card_sub_eq_one (x : ℕ) :
    Polynomial.coeff (∏ x1 in Finset.attach (Finset.range (S.toFinset.card - rootMultiplicity 1
    (auxPolynomial 𝒜 ℳ μ S) - 1)), (Polynomial.X - (@Nat.cast ℚ[X] NonAssocSemiring.toNatCast x)
    + ↑↑x1 + 1)) (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1) = 1 := by
  let hcoeff := @Polynomial.coeff_prod_of_natDegree_le ℚ ({ x // x ∈ Finset.range (S.toFinset.card
    - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1) }) (Finset.attach (Finset.range
    (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1))) _ (fun x1 ↦ Polynomial.X
    - (@Nat.cast ℚ[X] NonAssocSemiring.toNatCast x) + ↑↑x1 + 1) 1 <| show ∀ x1 ∈ Finset.attach
    (Finset.range (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1)), natDegree
    (Polynomial.X - (@Nat.cast ℚ[X] NonAssocSemiring.toNatCast x) + ↑↑x1 + 1) ≤ 1 by
    intro x1 _; exact le_trans (Polynomial.natDegree_add_le _ _) <| by
      simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
      exact le_trans (Polynomial.natDegree_add_le _ _) <| by
        simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
        exact le_trans (Polynomial.natDegree_sub_le _ _) <| by
          simp only [natDegree_X, natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
  simp only [Finset.card_attach, Finset.card_range, mul_one, coeff_add, coeff_sub, coeff_X_one,
    coeff_nat_cast_ite, one_ne_zero, ↓reduceIte, CharP.cast_eq_zero, sub_zero, add_zero,
    Finset.prod_const] at hcoeff
  rw [hcoeff, Polynomial.coeff_one]; simp only [one_ne_zero, ↓reduceIte, add_zero, one_pow]

theorem hilbertPolynomial_natDegree_eq_sub (hhP : hilbertPolynomial 𝒜 ℳ μ S ≠ 0) :
    (hilbertPolynomial 𝒜 ℳ μ S).natDegree =
    S.toFinset.card - (Polynomial.rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S)) - 1 := by
  by_cases h : auxPolynomial 𝒜 ℳ μ S = 0
  · exfalso; rw [hilbertPolynomial] at hhP;
    simp only [h, ↓reduceDite, ne_eq, not_true_eq_false] at hhP
  · by_cases h1 : S.toFinset.card ≤ (auxPolynomial 𝒜 ℳ μ S).rootMultiplicity 1
    · rw [hilbertPolynomial] at hhP
      simp only [h1, ↓reduceIte, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hhP
    · refine' Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ _
      · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, h1, ↓reduceIte]
        rw [polynomial_of_polynomial]; simp only [zsmul_eq_mul]
        refine' @Polynomial.natDegree_sum_le_of_forall_le ℕ (Finset.range (natDegree
          (auxPolynomial' 𝒜 ℳ μ S h) + 1)) ℚ _ (S.toFinset.card - rootMultiplicity 1
          (auxPolynomial 𝒜 ℳ μ S) - 1) (fun x ↦ (@Int.cast ℚ[X] Ring.toIntCast (Polynomial.coeff
          (auxPolynomial' 𝒜 ℳ μ S h) x)) * prePolynomial (S.toFinset.card - rootMultiplicity 1
          (auxPolynomial 𝒜 ℳ μ S) - 1) x) _
        · intro i _
          refine' le_trans (@Polynomial.natDegree_mul_le ℚ _ (@Int.cast ℚ[X] Ring.toIntCast
            (Polynomial.coeff (auxPolynomial' 𝒜 ℳ μ S h) i)) (prePolynomial (S.toFinset.card -
            rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1) i)) _
          · simp only [natDegree_int_cast, zero_add]; rw [prePolynomial]
            simp only [Finset.univ_eq_attach, map_natCast]
            refine' le_trans (Polynomial.natDegree_smul_le (@Inv.inv ℚ _ (Nat.factorial
              (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1))) _) _
            · refine' le_trans (Polynomial.natDegree_prod_le (@Finset.attach ℕ (Finset.range
                (S.toFinset.card - rootMultiplicity 1 (auxPolynomial 𝒜 ℳ μ S) - 1))) _) _
              · have : ∀ x ∈ Finset.attach (Finset.range (S.toFinset.card - rootMultiplicity 1
                    (auxPolynomial 𝒜 ℳ μ S) - 1)), natDegree (Polynomial.X - (@Nat.cast ℚ[X]
                    NonAssocSemiring.toNatCast i) + ↑↑x + 1) ≤ 1 :=
                  λ x _ ↦ le_trans (Polynomial.natDegree_add_le _ _) <| by
                  simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
                  exact le_trans (Polynomial.natDegree_add_le _ _) <| by
                    simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
                    exact le_trans (Polynomial.natDegree_sub_le _ _) <| by simp only [natDegree_X,
                      natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
                exact le_trans (Finset.sum_le_sum this) <| by simp only [Finset.sum_const,
                  Finset.card_attach, Finset.card_range, smul_eq_mul, mul_one, le_refl]
      · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, h1, ↓reduceIte, ne_eq]
        rw [polynomial_of_polynomial]
        simp only [zsmul_eq_mul, finset_sum_coeff, coeff_intCast_mul]
        simp_rw [prePolynomial, Polynomial.coeff_smul]
        simp only [Finset.univ_eq_attach, map_natCast, smul_eq_mul]
        simp_rw [coeff_S_card_sub_eq_one 𝒜 ℳ μ S]; rw [← Finset.sum_mul]
        simp only [mul_one, mul_eq_zero, _root_.inv_eq_zero, Nat.cast_eq_zero]
        rw [not_or]; constructor
        · rw [show ∑ i in Finset.range (natDegree (auxPolynomial' 𝒜 ℳ μ S h) + 1), (@Int.cast ℚ
            Ring.toIntCast (coeff (auxPolynomial' 𝒜 ℳ μ S h) i)) = eval 1 (auxPolynomial'
            𝒜 ℳ μ S h) by rw [Polynomial.eval_eq_sum_range]; simp only [one_pow, mul_one,
            Int.cast_sum]]
          intro h'; simp only [Int.cast_eq_zero] at h'; rw [auxPolynomial'] at h'
          simp only [map_one, eval_mul, eval_pow, eval_neg, eval_one, Int.reduceNeg, mul_eq_zero,
            pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, rootMultiplicity_eq_zero_iff,
            IsRoot.def, not_forall, exists_prop, false_and, false_or] at h'
          let this := (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (auxPolynomial 𝒜 ℳ μ S)
            h 1).choose_spec.2
          rw [Polynomial.dvd_iff_isRoot] at this; exact this h'
        · exact Nat.factorial_ne_zero _

theorem exists_unique_polynomial :
    ∃! (p : Polynomial ℚ), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    (μ <| .of _ <| (ℳ n : Type u) : ℚ) = Polynomial.eval (n : ℚ) p)) :=
  ⟨hilbertPolynomial 𝒜 ℳ μ S, ⟨(auxPolynomial 𝒜 ℳ μ S).natDegree, fun n hn ↦
  additiveFunction_val_eq_hilbertPolynomial_eval 𝒜 ℳ μ S hS n hn⟩, λ q ⟨N, hqN⟩ ↦
  eq_of_infinite_eval_eq q (hilbertPolynomial 𝒜 ℳ μ S) <| λ hfin ↦
  Set.Infinite.image (Set.injOn_of_injective Nat.cast_injective _)
  (Set.Ioi_infinite (max N (natDegree (auxPolynomial 𝒜 ℳ μ S))))
  <| Set.Finite.subset hfin <| show @Nat.cast ℚ _ '' (Set.Ioi (max N
  (natDegree (auxPolynomial 𝒜 ℳ μ S)))) ⊆ (@setOf ℚ fun x ↦
  eval x q = eval x (hilbertPolynomial 𝒜 ℳ μ S)) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← additiveFunction_val_eq_hilbertPolynomial_eval
  𝒜 ℳ μ S hS n h2]; exact (Rat.ext (congrArg Rat.num (hqN n h1)) (congrArg Rat.den
  (hqN n h1))).symm⟩

end HilbertSerre
