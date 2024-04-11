/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.RingTheory.Polynomial.Hilbert
import Mathlib.Algebra.HilbertSerre.Theorem

/-!
# Hilbert polynomials

Remember the assumptions in the file `Mathlib/Algebra/HilbertSerre/Theorem.lean`:
`universe u`
`variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]`
`variable [noetherian_ring : IsNoetherianRing A] [finite_module : Module.Finite A M]`
`variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]`
`variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]`
`variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)`
`variable (S : generatingSetOverBaseRing 𝒜)`

This file inherits all the above settings. With an additional assumption
`hS : ∀ (i : S.toFinset), S.deg i.2 = 1`, the main things achieved in this file are:
1. formalising the Hilbert polynomial `HilbertSerre.hilbertPolynomial 𝒜 ℳ μ S : Polynomial ℚ`;
2. proving that for any large enough `n : ℕ`, the value of the additive function `μ` at `ℳ n`
   is equal to the value of the Hilbert polynomial at `n`;
3. showing that the polynomial `h` satisfying the above property (i.e. for any large enough
   `n : ℕ`, the value of `μ` at `ℳ n` equals the value of `h` at `n`) is unique;
4. proving a theorem `HilbertSerre.natDegree_hilbertPolynomial`, which tells us the specific
   degree of any non-zero Hilbert polynomial.
-/

universe u
variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable [noetherian_ring : IsNoetherianRing A] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜) (hS : ∀ (i : S.toFinset), S.deg i.2 = 1)

open BigOperators
open PowerSeries

namespace generatingSetOverBaseRing

lemma poles_eq_one_sub_pow_of_deg_eq_one :
    S.poles = ⟨1 - X, invOfUnit (1 - X) 1, mul_invOfUnit (1 - X) 1 <| by
    simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
    rw [mul_comm]; exact mul_invOfUnit (1 - X) 1 <| by simp only [map_sub, map_one,
    constantCoeff_X, sub_zero, Units.val_one]⟩ ^ S.toFinset.card := by
  rw [poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach]
  exact Units.eq_iff.mp rfl

end generatingSetOverBaseRing

namespace HilbertSerre

open Polynomial
open generatingSetOverBaseRing

/--
Remember the Hilbert Serre Theorem (`hilbert_serre`), which says that there exists some
`p : Polynomial ℤ` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`. This definition is the
polynomial `p` guaranteed by `hilbert_serre`.
-/
noncomputable def numeratorPolynomial : Polynomial ℤ := (hilbert_serre 𝒜 ℳ μ S).choose

theorem numeratorPolynomial_mul_inv_poles_eq_poincareSeries :
    (numeratorPolynomial 𝒜 ℳ μ S).ToPowerSeries * S.poles⁻¹ = μ.poincareSeries 𝒜 ℳ :=
  (hilbert_serre 𝒜 ℳ μ S).choose_spec.symm

/--
Assume that `numeratorPolynomial 𝒜 ℳ μ S ≠ 0`. The greatest factor of
`numeratorPolynomial 𝒜 ℳ μ S` that is not divided by `1 - X`.
-/
noncomputable def numeratorPolynomial' (hn0 : numeratorPolynomial 𝒜 ℳ μ S ≠ 0) : Polynomial ℤ :=
  ((- 1) ^ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (numeratorPolynomial 𝒜 ℳ μ S) hn0 1).choose

local notation "np'" => numeratorPolynomial' 𝒜 ℳ μ S

theorem pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial
    (hn0 : numeratorPolynomial 𝒜 ℳ μ S ≠ 0) :
    ((1 - Polynomial.X) ^ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) *
    (numeratorPolynomial' 𝒜 ℳ μ S hn0) = numeratorPolynomial 𝒜 ℳ μ S := by
  rw [numeratorPolynomial', ← mul_assoc, ← mul_pow]
  simp only [mul_neg, mul_one, neg_sub, map_one]
  exact id (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (numeratorPolynomial 𝒜 ℳ μ S)
    hn0 1).choose_spec.1.symm

theorem numeratorPolynomial'_ne_zero (hn0 : numeratorPolynomial 𝒜 ℳ μ S ≠ 0) :
    numeratorPolynomial' 𝒜 ℳ μ S hn0 ≠ 0 := λ h0 ↦ by
  let hpow := pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial 𝒜 ℳ μ S hn0
  rw [h0, mul_zero] at hpow; exact hn0 (id hpow.symm)

theorem natDegree_numeratorPolynomial'_le (hn0 : numeratorPolynomial 𝒜 ℳ μ S ≠ 0) :
    (numeratorPolynomial' 𝒜 ℳ μ S hn0).natDegree ≤ (numeratorPolynomial 𝒜 ℳ μ S).natDegree := by
  rw [← pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial _ _ _ _ _,
    natDegree_mul]
  exact (np' hn0).natDegree.le_add_left
    (natDegree ((1 - Polynomial.X) ^ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1))
  exact pow_ne_zero _ <| λ h0 ↦ by
    let this : Polynomial.coeff (1 - (X : ℤ[X])) 0 = 0 := by rw [h0]; simp only [coeff_zero]
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  exact numeratorPolynomial'_ne_zero 𝒜 ℳ μ S hn0

theorem natDegree_pow_rootMultiplicity_sub_mul_numeratorPolynomial'_le
    (h : numeratorPolynomial 𝒜 ℳ μ S ≠ 0)
    (h1 : S.toFinset.card ≤ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) :
    ((1 - Polynomial.X) ^ ((numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 - S.toFinset.card) *
    numeratorPolynomial' 𝒜 ℳ μ S h).natDegree ≤ (numeratorPolynomial 𝒜 ℳ μ S).natDegree := by
  let this := pow_ne_zero ((numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 - S.toFinset.card)
    <| λ (h0 : 1 - (X : ℤ[X]) = 0) ↦ by
    let this : (1 - (X : ℤ[X])).coeff 0 = 0 := by rw [h0, coeff_zero]
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  rw [show (numeratorPolynomial 𝒜 ℳ μ S).natDegree = (((1 - Polynomial.X) ^
    ((numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 - S.toFinset.card + S.toFinset.card)) *
    numeratorPolynomial' 𝒜 ℳ μ S h).natDegree by rw [← Nat.eq_add_of_sub_eq h1 rfl,
    pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial], pow_add, mul_assoc,
    mul_comm ((1 - Polynomial.X) ^ S.toFinset.card), ← mul_assoc, natDegree_mul, natDegree_mul,
    natDegree_mul]
  simp only [natDegree_pow, le_add_iff_nonneg_right, zero_le]
  · exact this
  · exact numeratorPolynomial'_ne_zero 𝒜 ℳ μ S h
  · rw [mul_ne_zero_iff]; exact ⟨this, numeratorPolynomial'_ne_zero 𝒜 ℳ μ S h⟩
  · exact pow_ne_zero _ <| λ h0 ↦ by
      let this : (1 - (X : ℤ[X])).coeff 0 = 0 := by rw [h0, coeff_zero]
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact this
  · exact numeratorPolynomial'_ne_zero 𝒜 ℳ μ S h

/--
The Hilbert polynomial, i.e. the polynomial such that for any `n : ℕ` which
is big enough, the value of `μ` at `ℳ n` is equal to its value at `n`.
-/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  if h : numeratorPolynomial 𝒜 ℳ μ S = 0 then 0
  else (if S.toFinset.card ≤ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 then 0
  else Polynomial.hilbert (numeratorPolynomial' 𝒜 ℳ μ S h)
  (S.toFinset.card - ((numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) - 1))

/--
The key property of the Hilbert polynomial, i.e. for any `n : ℕ` that is large enough,
the value of `μ` at `ℳ n` is equal to the value of the Hilbert polynomial at `n`.
-/
theorem AdditiveFunction_eq_hilbertPolynomial_eval
    (n : ℕ) (hn : (numeratorPolynomial 𝒜 ℳ μ S).natDegree < n) :
    (μ <| .of _ <| (ℳ n : Type u) : ℚ) =
    (hilbertPolynomial 𝒜 ℳ μ S).eval (n : ℚ) := by
  have hμ : μ (FGModuleCat.of (𝒜 0) (ℳ n)) = coeff ℤ n (μ.poincareSeries 𝒜 ℳ) := by
    rw [AdditiveFunction.poincareSeries, coeff_mk]
  by_cases h : numeratorPolynomial 𝒜 ℳ μ S = 0
  · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, eval_zero, Int.cast_eq_zero]
    rw [hμ, ← numeratorPolynomial_mul_inv_poles_eq_poincareSeries 𝒜 ℳ μ S, h]
    simp only [coe_zero, val_inv_poles, zero_mul]; exact rfl
  · rw [hilbertPolynomial, hμ]; simp only [h, ↓reduceDite]
    let one_sub : ℤ⟦X⟧ˣ := ⟨1 - PowerSeries.X, invOfUnit (1 - PowerSeries.X) 1,
      @mul_invOfUnit ℤ _ (1 - PowerSeries.X) 1 <| by
      simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
      rw [mul_comm]; exact @mul_invOfUnit ℤ _ (1 - PowerSeries.X) 1 <| by
        simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one]⟩
    have one_sub_eq : 1 - PowerSeries.X = (1 - (X : ℤ[X])).ToPowerSeries := by
      rw [PowerSeries.ext_iff]; exact λ i ↦ by_cases (λ (hi : i = 0) ↦ by
        simp only [hi, map_sub, PowerSeries.coeff_one, ↓reduceIte, coeff_zero_X, sub_zero,
        map_one, coeff_coe, coeff_sub, coeff_one_zero, coeff_X_zero]) (λ hi ↦ by
        simp only [map_sub, PowerSeries.coeff_one, hi, ↓reduceIte, zero_sub, map_one, coeff_coe,
        coeff_sub]; rw [Polynomial.coeff_one]; simp only [hi, ↓reduceIte, zero_sub, neg_inj];
        rw [Polynomial.coeff_X, PowerSeries.coeff_X]; exact by_cases (λ (hi : i = 1) ↦ by
        simp only [hi, ↓reduceIte]) (λ hi ↦ by
        simp only [hi, ↓reduceIte]; exact Eq.symm (if_neg (Ne.symm hi))))
    by_cases h1 : S.toFinset.card ≤ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1
    · simp only [h1, ↓reduceIte, eval_zero, Int.cast_eq_zero]
      rw [← numeratorPolynomial_mul_inv_poles_eq_poincareSeries 𝒜 ℳ μ S,
        ← pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial 𝒜 ℳ μ S h,
        show poles S = one_sub ^ S.toFinset.card by
        rw [poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach];
        exact Units.eq_iff.mp rfl, coe_mul, coe_pow, show @ToPowerSeries ℤ
        Int.instCommSemiringInt (1 - Polynomial.X) = one_sub.val by
        simp only; rw [one_sub_eq], ← mul_comm, ← mul_assoc, ← Units.val_pow_eq_pow_val,
        ← Units.val_mul, mul_comm (one_sub ^ S.toFinset.card)⁻¹, ← pow_sub _ h1,
        Units.val_pow_eq_pow_val, show one_sub.val = (1 - (X : ℤ[X])).ToPowerSeries by
        simp only [map_one]; rw [one_sub_eq], ← coe_pow, ← coe_mul, coeff_coe]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_rootMultiplicity_sub_mul_numeratorPolynomial'_le 𝒜 ℳ μ S h h1) hn)
    · simp only [h1, ↓reduceIte]
      rw [← numeratorPolynomial_mul_inv_poles_eq_poincareSeries 𝒜 ℳ μ S, ← coe_inj.2 <|
        pow_rootMultiplicity_mul_numeratorPolynomial'_eq_numeratorPolynomial 𝒜 ℳ μ S h, coe_mul,
        coe_pow, ← one_sub_eq, show poles S = one_sub ^ S.toFinset.card by
        exact poles_eq_one_sub_pow_of_deg_eq_one 𝒜 S hS, mul_comm, ← mul_assoc,
        show (1 - (X : ℤ⟦X⟧)) = one_sub by simp only, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← inv_pow_sub one_sub <| Nat.le_of_not_ge h1, ← coeff_mul_invOneSubPow_eq_hilbert_eval
        _ _ _ (le_trans (natDegree_numeratorPolynomial'_le 𝒜 ℳ μ S h) <| Nat.lt_succ.mp
        (Nat.le.step hn)), show one_sub⁻¹ ^ (S.toFinset.card - (numeratorPolynomial
        𝒜 ℳ μ S).rootMultiplicity 1) = invOneSubPow (S.toFinset.card - (numeratorPolynomial
        𝒜 ℳ μ S).rootMultiplicity 1 - 1) by
        rw [invOneSubPow_eq_inv_one_sub_pow, Nat.sub_add_cancel]; exact Nat.le_sub_of_add_le'
          (Nat.not_le.mp h1), mul_comm (numeratorPolynomial' 𝒜 ℳ μ S h).ToPowerSeries]

/--
The Hilbert polynomial is unique. In other words, for any `h : Polynomial ℚ`, if `h` satisfies
the key property of the Hilbert polynomial (i.e. for any large enough `n : ℕ`, the value of `μ`
at `ℳ n` equals the value of `h` at `n`), then `h` is the Hilbert polynomial itself.
-/
theorem exists_unique_hilbertPolynomial :
    ∃! (h : Polynomial ℚ), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    (μ <| .of _ <| (ℳ n : Type u) : ℚ) = h.eval (n : ℚ))) :=
  ⟨hilbertPolynomial 𝒜 ℳ μ S, ⟨(numeratorPolynomial 𝒜 ℳ μ S).natDegree, fun n hn ↦
  AdditiveFunction_eq_hilbertPolynomial_eval 𝒜 ℳ μ S hS n hn⟩, λ q ⟨N, hqN⟩ ↦
  eq_of_infinite_eval_eq q (hilbertPolynomial 𝒜 ℳ μ S) <| λ hfin ↦ Set.Infinite.image
  (Set.injOn_of_injective Nat.cast_injective _) (Set.Ioi_infinite (max N (natDegree
  (numeratorPolynomial 𝒜 ℳ μ S)))) <| Set.Finite.subset hfin <|
  show @Nat.cast ℚ _ '' (Set.Ioi (max N (natDegree (numeratorPolynomial 𝒜 ℳ μ S)))) ⊆
  (@setOf ℚ fun x ↦ eval x q = eval x (hilbertPolynomial 𝒜 ℳ μ S)) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← AdditiveFunction_eq_hilbertPolynomial_eval
  𝒜 ℳ μ S hS n h2]; exact (Rat.ext (congrArg Rat.num (hqN n h1)) (congrArg Rat.den
  (hqN n h1))).symm⟩

lemma prod_S_card_sub_sub_coeff_eq_one (x : ℕ) :
    coeff (∏ x1 in Finset.attach (Finset.range (S.toFinset.card - rootMultiplicity 1
    (numeratorPolynomial 𝒜 ℳ μ S) - 1)), (Polynomial.X - (x : ℚ[X]) + ↑↑x1 + 1))
    (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1) = 1 := by
  let hcoeff := @coeff_prod_of_natDegree_le ℚ ({ x // x ∈ Finset.range (S.toFinset.card -
    rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1) }) (Finset.attach (Finset.range
    (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1))) _ (fun x1 ↦
    Polynomial.X - (x : ℚ[X]) + ↑↑x1 + 1) 1 <| show ∀ x1 ∈ Finset.attach (Finset.range
    (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1)), natDegree
    (Polynomial.X - (x : ℚ[X]) + ↑↑x1 + 1) ≤ 1 by
    intro x1 _; exact le_trans (natDegree_add_le _ _) <| by
      simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
      exact le_trans (natDegree_add_le _ _) <| by
        simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
        exact le_trans (natDegree_sub_le _ _) <| by
          simp only [natDegree_X, natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
  simp only [Finset.card_attach, Finset.card_range, mul_one, coeff_add, coeff_sub, coeff_X_one,
    coeff_nat_cast_ite, one_ne_zero, ↓reduceIte, CharP.cast_eq_zero, sub_zero, add_zero,
    Finset.prod_const] at hcoeff
  rw [hcoeff, Polynomial.coeff_one]; simp only [one_ne_zero, ↓reduceIte, add_zero, one_pow]

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbertPolynomial (hhP : hilbertPolynomial 𝒜 ℳ μ S ≠ 0) :
    (hilbertPolynomial 𝒜 ℳ μ S).natDegree =
    S.toFinset.card - ((numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1) - 1 := by
  by_cases h : numeratorPolynomial 𝒜 ℳ μ S = 0
  · exfalso; rw [hilbertPolynomial] at hhP
    simp only [h, ↓reduceDite, ne_eq, not_true_eq_false] at hhP
  · by_cases h1 : S.toFinset.card ≤ (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1
    · rw [hilbertPolynomial] at hhP
      simp only [h1, ↓reduceIte, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hhP
    · refine' natDegree_eq_of_le_of_coeff_ne_zero _ _
      · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, h1, ↓reduceIte]
        rw [hilbert]; simp only [zsmul_eq_mul]
        refine' @natDegree_sum_le_of_forall_le ℕ (Finset.range (natDegree (numeratorPolynomial'
          𝒜 ℳ μ S h) + 1)) ℚ _ (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial
          𝒜 ℳ μ S) - 1) (fun x ↦ (@Int.cast ℚ[X] Ring.toIntCast (coeff (numeratorPolynomial'
          𝒜 ℳ μ S h) x)) * preHilbert (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial
          𝒜 ℳ μ S) - 1) x) _
        · intro i _
          refine' le_trans (@natDegree_mul_le ℚ _ (@Int.cast ℚ[X] _ (coeff (numeratorPolynomial'
            𝒜 ℳ μ S h) i)) (preHilbert (S.toFinset.card - rootMultiplicity 1 (numeratorPolynomial
            𝒜 ℳ μ S) - 1) i)) _
          · simp only [natDegree_int_cast, zero_add]; rw [preHilbert]
            simp only [Finset.univ_eq_attach, map_natCast]
            refine' le_trans (natDegree_smul_le (@Inv.inv ℚ _ (Nat.factorial (S.toFinset.card -
              rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1))) _) _
            · refine' le_trans (natDegree_prod_le (@Finset.attach ℕ (Finset.range (S.toFinset.card
                - rootMultiplicity 1 (numeratorPolynomial 𝒜 ℳ μ S) - 1))) _) _
              · have : ∀ x ∈ Finset.attach (Finset.range (S.toFinset.card - rootMultiplicity 1
                    (numeratorPolynomial 𝒜 ℳ μ S) - 1)), natDegree (Polynomial.X - (i : ℚ[X])
                    + ↑↑x + 1) ≤ 1 :=
                  fun x _ ↦ le_trans (natDegree_add_le _ _) <| by
                  simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
                  exact le_trans (natDegree_add_le _ _) <| by
                    simp only [natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left];
                    exact le_trans (natDegree_sub_le _ _) <| by simp only [natDegree_X,
                      natDegree_nat_cast, ge_iff_le, zero_le, max_eq_left, le_refl]
                exact le_trans (Finset.sum_le_sum this) <| by simp only [Finset.sum_const,
                  Finset.card_attach, Finset.card_range, smul_eq_mul, mul_one, le_refl]
      · rw [hilbertPolynomial]; simp only [h, ↓reduceDite, h1, ↓reduceIte, ne_eq]; rw [hilbert]
        simp only [zsmul_eq_mul, finset_sum_coeff, coeff_intCast_mul]
        simp_rw [preHilbert, Polynomial.coeff_smul]
        simp only [Finset.univ_eq_attach, map_natCast, smul_eq_mul]
        simp_rw [prod_S_card_sub_sub_coeff_eq_one 𝒜 ℳ μ S]; rw [← Finset.sum_mul]
        simp only [mul_one, mul_eq_zero, _root_.inv_eq_zero, Nat.cast_eq_zero]; rw [not_or]
        constructor
        · rw [show ∑ i in Finset.range (natDegree (numeratorPolynomial' 𝒜 ℳ μ S h) + 1),
            (@Int.cast ℚ Ring.toIntCast (coeff (numeratorPolynomial' 𝒜 ℳ μ S h) i)) = eval 1
            (numeratorPolynomial' 𝒜 ℳ μ S h) by rw [eval_eq_sum_range]; simp only [one_pow,
            mul_one, Int.cast_sum]]
          intro h'; simp only [Int.cast_eq_zero] at h'; rw [numeratorPolynomial'] at h'
          simp only [map_one, eval_mul, eval_pow, eval_neg, eval_one, Int.reduceNeg, mul_eq_zero,
            pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, rootMultiplicity_eq_zero_iff,
            IsRoot.def, not_forall, exists_prop, false_and, false_or] at h'
          let this := (exists_eq_pow_rootMultiplicity_mul_and_not_dvd (numeratorPolynomial
            𝒜 ℳ μ S) h 1).choose_spec.2
          rw [dvd_iff_isRoot] at this; exact this h'
        · exact Nat.factorial_ne_zero _

end HilbertSerre
