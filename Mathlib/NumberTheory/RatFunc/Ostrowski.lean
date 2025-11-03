/-
Copyright (c) 2025 María Inés de Frutos-Fernández & Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Ostrowski's theorem for `K(X)`

This file proves Ostrowski's theorem for the field of rational functions `Fq(X)`, where `Fq` is any
field: if `v` is a discrete valuation on `Fq(X)` which is trivial on elements of `Fq`, then `v` is
equivalent to either the `I`-adic valuation for some `I : HeightOneSpectrum Fq[X]`, or to the
valuation at infinity `FunctionField.inftyValuation Fq`.

## Main results
- `RatFunc.valuation_isEquiv_infty_or_adic`: Ostrowski's theorem for `Fq(X)`.
- `RatFunc.valuation_isEquiv_infty_or_adic_of_fintype`: Ostrowski's theorem for `Fq(X)`, where `Fq`
is a finite field.
-/

noncomputable section

open Multiplicative RatFunc WithZero

lemma FiniteField.valuation_algebraMap_eq_one {Fq A Γ₀ : Type*} [Field Fq] [Fintype Fq]
    [Ring A] [Algebra Fq A] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation A Γ₀) (a : Fq)
    (ha : a ≠ 0) : v ((algebraMap Fq A) a) = 1 := by
  have hpow : (v ((algebraMap Fq A) a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, pow_card_sub_one_eq_one a ha]
  refine (pow_eq_one_iff ?_).mp hpow
  grind [Fintype.one_lt_card]

variable {Fq Γ : Type*} [Field Fq] [LinearOrderedCommGroupWithZero Γ]
  {v : Valuation (RatFunc Fq) Γ}

namespace RatFunc

section Infinity

open FunctionField Polynomial Valuation

theorem valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X {f : RatFunc Fq}
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1)
    (hlt : 1 < v X) (hf : f ≠ 0) : v f = v RatFunc.X ^ f.intDegree := by
  induction f using RatFunc.induction_on with
  | f p q hne0 =>
    rw [intDegree_div (by grind only) (by grind only), v.map_div, zpow_sub₀ (ne_zero_of_lt hlt)]
    simp_rw [intDegree_polynomial, zpow_natCast, ← coe_polynomial_eq_algebraMap]
    have hp : p ≠ 0  := by contrapose! hf; simp [hf]
    congr <;> exact valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ h hlt ‹_›

variable [DecidableEq (RatFunc Fq)]

theorem valuation_isEquiv_inftyValuation_of_one_lt_valuation_X
    (h : ∀ a : Fq, a ≠ 0 → v (C a) = 1) (hlt : 1 < v X) : v.IsEquiv (inftyValuation Fq) := by
  refine isEquiv_iff_val_lt_one.mpr fun {f} ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hlt' : 1 < inftyValuation Fq X := by simp [← exp_zero]
    rw [valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X h hlt hf,
      valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
        (fun _ ha ↦ by simp [inftyValuation.C _ ha]) hlt' hf]
    grind [one_le_zpow_iff_right₀]

end Infinity

open IsDedekindDomain HeightOneSpectrum Set Valuation FunctionField Polynomial

theorem setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty [v.IsNontrivial]
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1) (hle : v RatFunc.X ≤ 1) :
    {p : Fq[X] | v p < 1 ∧ p ≠ 0}.Nonempty := by
  obtain ⟨w , h0, h1⟩ := IsNontrivial.exists_lt_one (v := v)
  rw [Valuation.ne_zero_iff] at h0
  induction w using RatFunc.induction_on with
  | f p q =>
    simp only [ne_eq, RatFunc.algebraMap_eq_C, _root_.div_eq_zero_iff,
      FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀] at *
    have hor : ¬v ↑p = 1 ∨ ¬v ↑q = 1 := by rw [← not_and_or]; aesop
    suffices ∀ r : Fq[X], v (↑r) ≠ 1 → r ≠ 0 → {p : Fq[X] | v ↑p < 1 ∧ ¬p = 0}.Nonempty by
      exact Or.elim hor (fun hp ↦ this p hp h0.1) (fun hq ↦ this q hq h0.2)
    exact fun r hr hr0 ↦ ⟨r, lt_iff_le_and_ne.mpr
      ⟨Polynomial.valuation_le_one_of_valuation_X_le_one _ h hle r, hr⟩, hr0⟩

private lemma one_le_valuation_factor (hne : {p : Fq[X] | v p < 1 ∧ p ≠ 0}.Nonempty) {a b : Fq[X]}
    (hab : v ↑(a * b) < 1 ∧ a ≠ 0 ∧ b ≠ 0) (hπᵥ : (degree_lt_wf.min _ hne) = a * b)
    (hb : ¬IsUnit b) : 1 ≤ v ↑a := by
  set πᵥ := (degree_lt_wf.min _ hne)
  have hda : a.degree < πᵥ.degree := by
    have hbpos := degree_pos_of_ne_zero_of_nonunit hab.2.2 hb
    simp_rw [hπᵥ, degree_mul, degree_eq_natDegree hab.2.1, degree_eq_natDegree hab.2.2] at hbpos ⊢
    norm_cast
    simpa using hbpos
  have hlea := imp_not_comm.mp (degree_lt_wf.not_lt_min _ hne) hda
  grind

private theorem irreducible_min_polynomial_valuation_lt_one_and_ne_zero
    (hne : {p : Fq[X] | v p < 1 ∧ p ≠ 0}.Nonempty)
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1) :
    Irreducible (degree_lt_wf.min {p : Fq[X] | v p < 1 ∧ p ≠ 0} hne) := by
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
    simp only [coe_polynomial_eq_algebraMap, map_mul] at hπᵥ this
    grind

section valuation_X_le_one

variable (hle : v RatFunc.X ≤ 1) (h : ∀ (a : Fq), a ≠ 0 → v ((algebraMap Fq (RatFunc Fq)) a) = 1)
   [v.IsNontrivial]

/-- A uniformizing element for the valuation `v`, as a polynomial in `Fq[X]`. -/
abbrev uniformizingPolynomial : Fq[X] :=
  WellFounded.min degree_lt_wf _ (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty h hle)

/-- A uniformizing element for the valuation `v`, as a polynomial in `Fq[X]`. -/
local notation "πᵥ" => uniformizingPolynomial hle h

lemma uniformizingPolynomial_ne_zero : πᵥ ≠ 0 := by
  have := degree_lt_wf.min_mem _ (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty h hle)
  simp_all [uniformizingPolynomial]

open Ideal in
/-- The maximal ideal of `Fq[X]` generated by the `uniformizingPolynomial` for `v`. -/
def valuationIdeal : HeightOneSpectrum Fq[X] where
  asIdeal := Submodule.span Fq[X] {πᵥ}
  isPrime := IsMaximal.isPrime (PrincipalIdealRing.isMaximal_of_irreducible
    (irreducible_min_polynomial_valuation_lt_one_and_ne_zero
      (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty h hle) h))
  ne_bot := by simpa using uniformizingPolynomial_ne_zero hle h

/-- The maximal ideal of `Fq[X]` generated by the `uniformizingPolynomial` for `v`. -/
local notation "Pᵥ" => RatFunc.valuationIdeal hle h

section Associates

open EuclideanDomain in
theorem valuation_eq_valuation_πᵥ_pow_of_valuation_X_le_one
    [DecidableEq (Associates (Ideal Fq[X]))]
    [(p : Associates (Ideal Fq[X])) → Decidable (Irreducible p)] (p : Fq[X]) (hp : p ≠ 0) :
    v (algebraMap Fq[X] (RatFunc Fq) p) = v (πᵥ ^ ((Associates.mk (Pᵥ).asIdeal).count
      (Associates.mk (Ideal.span {p})).factors)) := by
  set π := πᵥ
  have hne := setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty h hle
  have hπirr : Irreducible π := irreducible_min_polynomial_valuation_lt_one_and_ne_zero hne h
  obtain ⟨k, q, hnq, heq⟩ := WfDvdMonoid.max_power_factor hp hπirr
  have hπ : π ∈ _ := degree_lt_wf.min_mem _ hne
  simp only [ne_eq, mem_setOf] at hπ
  nth_rw 1 [heq]
  simp only [map_mul, map_pow]
  suffices v (algebraMap Fq[X] (RatFunc Fq) q) = 1 by
    simp only [this, mul_one]
    congr
    exact (Ideal.count_associates_eq (irreducible_iff_prime.mp hπirr) hnq heq).symm
  rw [← mod_add_div q π, map_add]
  rw [← mod_eq_zero] at hnq
  suffices v (algebraMap Fq[X] (RatFunc Fq) (q % π)) = 1 ∧
      v (algebraMap Fq[X] (RatFunc Fq) (π * (q / π))) < 1 by
    obtain ⟨h₁, h₂⟩ := this
    rw [← h₁] at h₂ ⊢
    exact Valuation.map_add_eq_of_lt_left _ h₂
  constructor
  · rw [← coe_polynomial_eq_algebraMap]
    have hnπ : q % π ∉ _ :=
      imp_not_comm.mp (degree_lt_wf.not_lt_min _ hne) (EuclideanDomain.remainder_lt q hπ.2)
    have := Polynomial.valuation_le_one_of_valuation_X_le_one _ h hle (q % π)
    grind
  · simpa only [map_mul, ← coe_polynomial_eq_algebraMap]
      using mul_lt_one_of_lt_of_le hπ.1 <| (q / π).valuation_le_one_of_valuation_X_le_one _ h hle

theorem uniformizingPolynomial_isUniformizer [vDisc : IsRankOneDiscrete v] :
    v.IsUniformizer (↑πᵥ) := by
  classical
  simp only [IsUniformizer]
  obtain ⟨x, hx⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  set y := (x : RatFunc Fq) with hy
  revert hx
  induction y using RatFunc.induction_on with
  | f p q hne0 =>
    intro hx
    have hp : p ≠ 0 := by
      have := hx.ne_zero
      grind [FaithfulSMul.algebraMap_eq_zero_iff]
    simp only [IsUniformizer, map_div₀] at hx
    rw [valuation_eq_valuation_πᵥ_pow_of_valuation_X_le_one hle h p hp,
      valuation_eq_valuation_πᵥ_pow_of_valuation_X_le_one hle h q hne0] at hx
    generalize hn : (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {p})).factors = n
    generalize hm : (Associates.mk (Pᵥ).asIdeal).count (Associates.mk (Ideal.span {q})).factors = m
    simp only [hn, map_pow, hm] at hx
    clear hn hm
    have hpi0 : v ↑πᵥ ≠ 0 := by simpa using uniformizingPolynomial_ne_zero hle h
    simp only [← zpow_natCast_sub_natCast₀ hpi0,
      ← IsRankOneDiscrete.valueGroup_genLTOne_eq_generator] at hx ⊢
    set pi' : Γˣ := Units.mk0 _ hpi0
    have hpi' : v ↑πᵥ = pi' := by rw [Units.val_mk0]
    simp only [hpi', ← Units.val_zpow_eq_zpow_val, Units.val_inj] at hx ⊢
    apply LinearOrderedCommGroup.Subgroup.genLTOne_unique
    · rw  [← Units.val_lt_val, ← hpi', Units.val_one]
      exact (WellFounded.min_mem degree_lt_wf _
        (setOf_polynomial_valuation_lt_one_and_ne_zero_nonempty h hle)).1
    · apply le_antisymm
      · intro g hg
        apply MonoidWithZeroHom.mem_valueGroup
        obtain ⟨k, hk⟩ := hg
        use ↑πᵥ ^ k
        rw [map_zpow₀, hpi', ← Units.val_zpow_eq_zpow_val, ← hk]
      · rw [← LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top
          (MonoidWithZeroHom.valueGroup v), ← hx]
        exact Subgroup.zpowers_le_of_mem (Subgroup.zpow_mem_zpowers pi' ((n : ℤ) - m))

theorem valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one [IsRankOneDiscrete v] :
    v.IsEquiv ((Pᵥ).valuation (RatFunc Fq)) := by
  classical
  rw [isEquiv_iff_val_le_one]
  intro f
  by_cases hf0 : f = 0
  · simp_all
  · induction f using RatFunc.induction_on with
    | f p q hq0 =>
      have hp0 : p ≠ 0 := by simp_all
      set pi := πᵥ with hpi_def
      have hpi : v.IsUniformizer (pi : RatFunc Fq) := uniformizingPolynomial_isUniformizer hle h
      simp only [map_div₀, valuation_of_algebraMap, intValuation_def, exp_neg, if_neg hp0,
        if_neg hq0, div_inv_eq_mul]
      rw [valuation_eq_valuation_πᵥ_pow_of_valuation_X_le_one hle h p hp0,
        valuation_eq_valuation_πᵥ_pow_of_valuation_X_le_one hle h q hq0]
      simp_all [div_le_one₀, inv_mul_le_one₀,
        (pow_le_pow_iff_right_of_lt_one₀ (by simp_all) (IsRankOneDiscrete.generator_lt_one v))]

end Associates

end valuation_X_le_one

theorem adicValuation_not_isEquiv_infty_valuation [DecidableEq (RatFunc Fq)]
    (p : IsDedekindDomain.HeightOneSpectrum Fq[X]) :
    ¬ (p.valuation (RatFunc Fq)).IsEquiv (inftyValuation Fq) := by
  simp only [isEquiv_iff_val_lt_one, not_forall]
  use 1/X
  simp only [_root_.not_iff, not_lt]
  have hlt : inftyValuation Fq (1/X) < 1 := by
    rw [one_div, map_inv₀, inftyValuation.X, inv_lt_one_iff₀]
    simp [← exp_zero]
  have hge : 1 ≤ (p.valuation (RatFunc Fq)) (1/X) := by
    simp only [one_div, map_inv₀, one_le_inv_iff₀]
    exact ⟨lt_of_le_of_ne zero_le' (Ne.symm ((p.valuation _).ne_zero_iff.mpr X_ne_zero)),
      p.valuation_le_one (Polynomial.X)⟩
  tauto

theorem adicValuation_ne_inftyValuation [DecidableEq (RatFunc Fq)]
   (p : IsDedekindDomain.HeightOneSpectrum Fq[X]) :
    p.valuation (RatFunc Fq) ≠ inftyValuation Fq := by
  by_contra h
  exact absurd Valuation.IsEquiv.refl (h ▸ RatFunc.adicValuation_not_isEquiv_infty_valuation p)

section Discrete

variable [IsRankOneDiscrete v]

theorem valuation_isEquiv_adic_of_valuation_X_le_one (hle : v X ≤ 1)
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1) :
    ∃ (u : HeightOneSpectrum Fq[X]), v.IsEquiv (u.valuation _) := by
  classical exact ⟨RatFunc.valuationIdeal hle h,
    valuation_isEquiv_valuationIdeal_adic_of_valuation_X_le_one hle h⟩

/-- Ostrowski's Theorem for `Fq(t)` with `Fq` any field. -/
theorem valuation_isEquiv_infty_or_adic [DecidableEq (RatFunc Fq)]
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1) :
    Xor' (v.IsEquiv (FunctionField.inftyValuation Fq))
      (∃! (u : HeightOneSpectrum Fq[X]), v.IsEquiv (u.valuation _)) := by
  by_cases hlt : 1 < v X
  /- Infinity case -/
  · have hv := valuation_isEquiv_inftyValuation_of_one_lt_valuation_X h hlt
    left
    use hv
    simp only [ExistsUnique, not_exists, not_and, not_forall]
    intro pw hw
    exact absurd (hw.symm.trans hv) (RatFunc.adicValuation_not_isEquiv_infty_valuation pw)
  /- Prime case -/
  · right; push_neg at hlt
    obtain ⟨pw, hw⟩ := valuation_isEquiv_adic_of_valuation_X_le_one hlt h
    exact ⟨⟨pw, hw, fun pw' hw' ↦ eq_of_valuation_isEquiv_valuation (hw'.symm.trans hw)⟩,
      fun hv ↦ absurd (hw.symm.trans hv) (RatFunc.adicValuation_not_isEquiv_infty_valuation pw)⟩

theorem valuation_isEquiv_adic_of_not_isEquiv_infty [DecidableEq (RatFunc Fq)]
    (h : ∀ a : Fq, a ≠ 0 → v (algebraMap Fq (RatFunc Fq) a) = 1)
    (hni : ¬ v.IsEquiv (FunctionField.inftyValuation Fq)) :
    ∃! (u : HeightOneSpectrum Fq[X]), v.IsEquiv (u.valuation _) :=
  (valuation_isEquiv_infty_or_adic h).or.resolve_left hni

section Fintype

variable [Fintype Fq]

variable (v) in
/-- Ostrowski's Theorem for `Fq(t)` with `Fq` a finite field. -/
theorem valuation_isEquiv_infty_or_adic_of_fintype [DecidableEq (RatFunc Fq)] :
    Xor' (v.IsEquiv (FunctionField.inftyValuation Fq))
      (∃! (u : HeightOneSpectrum Fq[X]), v.IsEquiv (u.valuation _)) :=
  valuation_isEquiv_infty_or_adic (FiniteField.valuation_algebraMap_eq_one v)

theorem valuation_isEquiv_adic_of_not_isEquiv_infty_of_fintype [DecidableEq (RatFunc Fq)]
    (hv : ¬ v.IsEquiv (FunctionField.inftyValuation Fq)) :
    ∃! (u : HeightOneSpectrum Fq[X]), v.IsEquiv (u.valuation _) :=
  (valuation_isEquiv_infty_or_adic_of_fintype v).or.resolve_left hv

end Fintype

end Discrete

end RatFunc
