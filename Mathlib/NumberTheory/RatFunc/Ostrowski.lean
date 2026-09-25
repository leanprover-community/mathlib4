/-
Copyright (c) 2025 María Inés de Frutos-Fernández & Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.FieldTheory.Finite.Valuation
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Ostrowski's theorem for `K(X)`

This file proves Ostrowski's theorem for the field of rational functions `K(X)`, where `K` is any
field: if `v` is a discrete valuation on `K(X)` which is trivial on elements of `K`, then `v` is
equivalent to either the `I`-adic valuation for some `I : HeightOneSpectrum K[X]`, or to the
valuation at infinity `FunctionField.inftyValuation K`.

## Main results
- `RatFunc.valuation_isEquiv_infty_or_adic`: Ostrowski's theorem for `K(X)`.
-/

@[expose] public noncomputable section


open Multiplicative WithZero

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation (RatFunc K) Γ}

namespace RatFunc

section Infinity

open FunctionField Polynomial Valuation

lemma valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc K}
    [v.IsTrivialOn K] (hlt : 1 < v X) (hf : f ≠ 0) : v f = v RatFunc.X ^ f.intDegree := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    rw [intDegree_div (by grind only) (by grind only), v.map_div, zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coePolynomial_eq_algebraMap]
    have hp : p ≠ 0  := by contrapose! hf; simp [hf]
    rw [valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hp,
      valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt hq]

variable [DecidableEq (RatFunc K)]

lemma valuation_isEquiv_inftyValuation_of_one_lt_valuation_X [v.IsTrivialOn K] (hlt : 1 < v X) :
    v.IsEquiv (inftyValuation K) := by
  refine isEquiv_iff_val_lt_one.mpr fun {f} ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation K X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt hf,
      valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X hlt' hf]
    grind [one_le_zpow_iff_right₀]

end Infinity

open IsDedekindDomain HeightOneSpectrum Set Valuation FunctionField Polynomial

lemma setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial] [v.IsTrivialOn K]
    (hle : v RatFunc.X ≤ 1) : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty := by
  obtain ⟨w , h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, _root_.div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or,
      map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aesop
    suffices ∀ r : K[X], v (↑r) ≠ 1 → r ≠ 0 → {p : K[X] | v ↑p < 1 ∧ ¬p = 0}.Nonempty by
      exact Or.elim hor (fun hp ↦ this p hp h0.1) (fun hq ↦ this q hq h0.2)
    exact fun r hr hr0 ↦ ⟨r, lt_iff_le_and_ne.mpr
      ⟨Polynomial.valuation_le_one_of_valuation_X_le_one _ hle r, hr⟩, hr0⟩

private lemma one_le_valuation_factor (hne : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty) {a b : K[X]}
    (hab : v ↑(a * b) < 1 ∧ a ≠ 0 ∧ b ≠ 0) (hπᵥ : degree_lt_wf.min _ hne = a * b)
    (hb : ¬IsUnit b) : 1 ≤ v ↑a := by
  set πᵥ := degree_lt_wf.min _ hne
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_comm.mp (degree_lt_wf.not_lt_min _) hda
  grind

lemma irreducible_min_polynomial_valuation_lt_one_and_ne_zero [v.IsTrivialOn K]
    (hne : {p : K[X] | v p < 1 ∧ p ≠ 0}.Nonempty) :
    Irreducible (degree_lt_wf.min {p : K[X] | v p < 1 ∧ p ≠ 0} hne) := by
  set πᵥ := degree_lt_wf.min _ hne
  have hπᵥ : v πᵥ < 1 ∧ πᵥ ≠ 0 := degree_lt_wf.min_mem _ hne
  refine irreducible_iff.mpr ⟨?_, fun a b hab ↦ ?_⟩
  · simp only [Polynomial.isUnit_iff, isUnit_iff_ne_zero]
    intro ⟨a, ha0, ha⟩
    rw [← ha, coePolynomial, algebraMap_C, ← algebraMap_eq_C] at hπᵥ
    grind
  · by_contra! H
    simp only [hab, ne_eq, mul_eq_zero, not_or] at hπᵥ
    have hva := one_le_valuation_factor hne hπᵥ hab H.2
    simp only [mul_comm a b, @and_comm (¬a = 0)] at hπᵥ hab
    have := Right.one_le_mul (one_le_valuation_factor hne hπᵥ hab H.1) hva
    simp only [coePolynomial_eq_algebraMap, map_mul] at hπᵥ this
    grind

section valuation_X_le_one

variable [v.IsNontrivial] [v.IsTrivialOn K] (hle : v RatFunc.X ≤ 1)

/-- A uniformizing element for the valuation `v`, as a polynomial in `K[X]`. -/
abbrev uniformizingPolynomial : K[X] :=
  WellFounded.min degree_lt_wf _ (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)

@[inherit_doc]
local notation "πᵥ" => uniformizingPolynomial hle

lemma uniformizingPolynomial_ne_zero : πᵥ ≠ 0 := by
  have := degree_lt_wf.min_mem _ (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)
  simp_all [uniformizingPolynomial]

lemma valuation_uniformizingPolynomial_lt_one : v πᵥ < 1 := by
  simpa using (degree_lt_wf.min_mem _
    (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)).1

open Ideal in
/-- The maximal ideal of `K[X]` generated by the `uniformizingPolynomial` for `v`. -/
def valuationIdeal : HeightOneSpectrum K[X] where
  asIdeal := Submodule.span K[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle)))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle

@[inherit_doc]
local notation "Pᵥ" => RatFunc.valuationIdeal hle

section Associates

open EuclideanDomain in
lemma valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one {p : K[X]}
    (hp : p ≠ 0) :
    v (algebraMap K[X] (RatFunc K) p) = v (πᵥ ^ ((Associates.mk (Pᵥ).asIdeal).count
      (Associates.mk (Ideal.span {p})).factors)) := by
  set π := πᵥ
  have hne := setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π ∈ _ := degree_lt_wf.min_mem _ hne
  simp only [ne_eq, mem_setOf] at hπ
  nth_rw 1 [heq]
  simp only [map_mul, map_pow]
  suffices v (algebraMap K[X] (RatFunc K) q) = 1 by
    simp only [this, mul_one]
    congr
    exact (Ideal.count_associates_eq (irreducible_iff_prime.mp hπirr) hnq heq).symm
  rw [← mod_add_div q π, map_add]
  rw [← mod_eq_zero] at hnq
  suffices v (algebraMap K[X] (RatFunc K) (q % π)) = 1 ∧
      v (algebraMap K[X] (RatFunc K) (π * (q / π))) < 1 by
    obtain ⟨h₁, h₂⟩ := this
    rw [← h₁] at h₂ ⊢
    exact Valuation.map_add_eq_of_lt_left _ h₂
  constructor
  · rw [← coePolynomial_eq_algebraMap]
    have hnπ : q % π ∉ {p : K[X] | v ↑p < 1 ∧ p ≠ 0} :=
      imp_not_comm.mp (degree_lt_wf.not_lt_min _) (EuclideanDomain.remainder_lt q hπ.2)
    have := Polynomial.valuation_le_one_of_valuation_X_le_one _ hle (q % π)
    grind
  · simpa only [map_mul, ← coePolynomial_eq_algebraMap]
      using mul_lt_one_of_lt_of_le hπ.1 <| (q / π).valuation_le_one_of_valuation_X_le_one _ hle

lemma exists_zpow_uniformizingPolynomial {f : RatFunc K} (hf : f ≠ 0) :
    ∃ (z : ℤ), v f = v πᵥ ^ z:= by
  have h0 : v πᵥ ≠ 0 := by simpa using uniformizingPolynomial_ne_zero hle
  induction f using RatFunc.induction_on with
  | f p q hq =>
    use (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors -
      (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).factors
    simp only [map_div₀, map_pow, zpow_sub₀ h0, zpow_natCast,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq,
      valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle
        (p := p) (by aesop)]

set_option backward.isDefEq.respectTransparency false in
lemma uniformizingPolynomial_isUniformizer [hv : IsRankOneDiscrete v] :
    v.IsUniformizer πᵥ := by
  have h0 : v πᵥ ≠ 0 := by simpa using uniformizingPolynomial_ne_zero hle
  rw [IsUniformizer, ← hv.valueGroup_genLTOne_eq_generator, ← h0.isUnit.unit_spec, Units.val_inj]
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
  · rw [← Units.val_lt_val, h0.isUnit.unit_spec, Units.val_one]
    exact valuation_uniformizingPolynomial_lt_one hle
  · ext γ
    simp only [coePolynomial_eq_algebraMap, MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq,
      map_eq_zero, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨a, ha, b, hab⟩ ↦ ?_⟩
    · use 1, one_ne_zero, πᵥ ^ k
      simp only [← Units.val_inj, Units.val_zpow_eq_zpow_val, h0.isUnit.unit_spec] at hk
      simp [← hk]
    · obtain ⟨ka, hka⟩ := exists_zpow_uniformizingPolynomial hle ha
      obtain ⟨kb, hkb⟩ := exists_zpow_uniformizingPolynomial hle (f := b) (by aesop)
      rw [hka, hkb] at hab
      use kb - ka
      have : v ↑πᵥ ^ ka ≠ 0 := zpow_ne_zero _ h0
      simp only [zpow_sub, ← Units.val_inj, Units.val_mul, Units.val_zpow_eq_zpow_val,
        h0.isUnit.unit_spec, Units.val_inv_eq_inv_val, ← hab, field]

lemma valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDiscrete v] :
    v.IsEquiv ((Pᵥ).valuation (RatFunc K)) := by
  rw [isEquiv_iff_val_le_one]
  intro f
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p ≠ 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc K) := uniformizingPolynomial_isUniformizer hle
      simp only [map_div₀, valuation_of_algebraMap, intValuation_def, exp_neg, if_neg hp0,
        if_neg hq0, div_inv_eq_mul]
      rw [valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hp0,
        valuation_eq_valuation_uniformizingPolynomial_pow_of_valuation_X_le_one hle hq0]
      simp_all [div_le_one₀, inv_mul_le_one₀,
        (pow_le_pow_iff_right_of_lt_one₀ (by simp_all) (IsRankOneDiscrete.generator_lt_one v))]

end Associates

end valuation_X_le_one

lemma adicValuation_not_isEquiv_infty_valuation [DecidableEq (RatFunc K)]
    (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    ¬ (p.valuation (RatFunc K)).IsEquiv (inftyValuation K) := by
  simp only [isEquiv_iff_val_le_one]
  push Not
  refine ⟨X, .inl ⟨p.valuation_le_one _, ?_⟩⟩
  rw [inftyValuation.X, ← log_lt_iff_lt_exp one_ne_zero, log_one]
  exact zero_lt_one

lemma adicValuation_ne_inftyValuation [DecidableEq (RatFunc K)]
   (p : IsDedekindDomain.HeightOneSpectrum K[X]) :
    p.valuation (RatFunc K) ≠ inftyValuation K := by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ adicValuation_not_isEquiv_infty_valuation p)

section Discrete

variable [IsRankOneDiscrete v]

section IsTrivialOn

variable [v.IsTrivialOn K]

lemma valuation_isEquiv_adic_of_valuation_X_le_one (hle : v X ≤ 1) :
    ∃ (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  ⟨_, valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle⟩

/-- **Ostrowski's Theorem** for `K(X)` with `K` any field:
A discrete valuation of rank 1 that is trivial on `K` is equivalent either to the valuation
at infinity or to the `p`-adic valuation for a unique maximal ideal `p` of `K[X]`. -/
theorem valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc K)] :
    Xor' (v.IsEquiv (FunctionField.inftyValuation K))
      (∃! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _)) := by
  rcases lt_or_ge 1 (v X) with hlt | hge
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
    refine .inl ⟨hv, ?_⟩
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)
  /- Prime case -/
  · obtain ⟨pw, hw⟩ := valuation_isEquiv_adic_of_valuation_X_le_one hge
    exact .inr ⟨⟨pw, hw, fun pw' hw' ↦ eq_of_valuation_isEquiv_valuation (hw'.symm.trans hw)⟩,
      fun hv ↦ absurd (hw.symm.trans hv) (adicValuation_not_isEquiv_infty_valuation pw)⟩

lemma valuation_isEquiv_adic_of_not_isEquiv_infty [DecidableEq (RatFunc K)]
    (hni : ¬ v.IsEquiv (FunctionField.inftyValuation K)) :
    ∃! (u : HeightOneSpectrum K[X]), v.IsEquiv (u.valuation _) :=
  valuation_isEquiv_infty_or_adic.or.resolve_left hni

end IsTrivialOn

end Discrete

end RatFunc

end
