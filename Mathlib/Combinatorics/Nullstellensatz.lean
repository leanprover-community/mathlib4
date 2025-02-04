/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod` :
  if `f` vanishes at any such point and `f.degreeOf s < (S s).ncard` for all `s`,
  then `f = 0`.

- `Polynomial.eq_zero_of_eval_zero` :
  a polynomial (in one indeterminate) which vanishes at more points than its degree
  is the zero polynomial.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h`,
  for some `h : σ →₀ MvPolynomial σ R` such that
  `((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

- `combinatorial_nullstellensatz_exists_eval_nonzero`
  a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
  `f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
  there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

## TODO

- Applications
- relation with Schwartz–Zippel lemma, as in [Rote_2023]

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]

- [Rote, *The Generalized Combinatorial Lason-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

open Finsupp

variable {R : Type*} [CommRing R]

theorem _root_.Polynomial.eq_zero_of_eval_zero [IsDomain R] (P : Polynomial R) (S : Set R)
    (Hdeg : Polynomial.natDegree P < S.ncard) (Heval : ∀ x ∈ S, P.eval x = 0) :
    P = 0 := by
  classical
  by_contra hP
  apply not_le.mpr Hdeg
  apply le_trans _ (Polynomial.card_roots' P)
  apply le_trans _ (Multiset.toFinset_card_le _)
  simp only [← Set.ncard_coe_Finset]
  apply Set.ncard_le_ncard _ P.roots.toFinset.finite_toSet
  intro s hs
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq,
    Polynomial.IsRoot.def]
  refine ⟨hP, Heval s hs⟩

namespace MvPolynomial

open Finsupp

theorem eq_zero_of_eval_zero_at_prod_nat {n : ℕ} [IsDomain R]
    (P : MvPolynomial (Fin n) R) (S : Fin n → Set R)
    (Hdeg : ∀ i, P.degreeOf i < (S i).ncard)
    (Heval : ∀ (x : Fin n → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction n generalizing R with
  | zero =>
    suffices P = C (constantCoeff P) by
      specialize Heval 0 (fun i ↦ False.elim (not_lt_zero' i.prop))
      rw [eval_zero] at Heval
      rw [this, Heval, map_zero]
    ext m
    suffices m = 0 by
      rw [this]
      simp only [← constantCoeff_eq, coeff_C, ↓reduceIte]
    ext d; exfalso; exact not_lt_zero' d.prop
  | succ n hrec =>
    let Q := finSuccEquiv R n P
    suffices Q = 0 by
      simp only [Q] at this
      rw [← AlgEquiv.symm_apply_apply (finSuccEquiv R n) P, this, map_zero]
    have Heval' : ∀ (x : Fin n → R) (_ : ∀ i, x i ∈ S i.succ),
      Polynomial.map (eval x) Q = 0 := fun x hx ↦ by
      apply Polynomial.eq_zero_of_eval_zero _ (S 0)
      · apply lt_of_le_of_lt _ (Hdeg 0)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [Q]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero, finSuccEquiv_coeff_coeff]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert Finset.le_sup hm
        simp only [cons_zero]
      · intro y hy
        rw [← eval_eq_eval_mv_eval']
        apply Heval
        intro i
        induction i using Fin.inductionOn with
        | zero => simp only [Fin.cons_zero, hy]
        | succ i _ => simp only [Fin.cons_succ]; apply hx
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by
      simp only [this, coeff_zero]
    apply hrec _ (fun i ↦ S (i.succ))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg i.succ)
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      simp only [Q, finSuccEquiv_coeff_coeff, ← ne_eq, ← MvPolynomial.mem_support_iff] at he
      convert Finset.le_sup he
      simp only [cons_succ]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

theorem weightedTotalDegree_rename_of_injective {σ τ : Type*} [DecidableEq τ] {e : σ → τ}
    {w : τ → ℕ} {P : MvPolynomial σ R} (he : Function.Injective e) :
    weightedTotalDegree w ((rename e) P) = weightedTotalDegree (w ∘ e) P := by
  unfold weightedTotalDegree
  rw [support_rename_of_injective he, Finset.sup_image]
  congr; ext; unfold weight; simp

theorem eq_zero_of_eval_zero_at_prod {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Set R)
    (Hdeg : ∀ i, P.degreeOf i < (S i).ncard)
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  suffices MvPolynomial.rename e P = 0 by
    have that := MvPolynomial.rename_injective (R := R) e (e.injective)
    rw [RingHom.injective_iff_ker_eq_bot] at that
    rwa [← RingHom.mem_ker, that] at this
  apply eq_zero_of_eval_zero_at_prod_nat _ (fun i ↦ S (e.symm i))
  · intro i
    classical
    convert Hdeg (e.symm i)
    conv_lhs => rw [← e.apply_symm_apply i, degreeOf_rename_of_injective e.injective]
  · intro x hx
    simp only [MvPolynomial.eval_rename]
    apply Heval
    intro s
    simp only [Function.comp_apply]
    convert hx (e s)
    simp only [Equiv.symm_apply_apply]

open MonomialOrder

/- Here starts the actual proof of the combinatorial Nullstellensatz -/

variable {σ : Type*}

/-- The polynomial in `X i` that vanishes at all elements of `S`. -/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r ∈ S, (X i - C r)

/-- The degree of `Alon.P S i` with respect to `X i` is the cardinality of `S`,
  and `0` otherwise. -/
private theorem Alon.degP [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i S.card := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_binomial i r)]
  · intro r _
    simp only [leadingCoeff_binomial, isRegular_one]

/-- The leading coefficient of `Alon.P S i` is `1`. -/
private theorem Alon.leadingCoeffP [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.leadingCoeff (P S i) = 1 := by
  simp only [P]
  rw [leadingCoeff_prod_of_regular ?_]
  · apply Finset.prod_eq_one
    intro r _
    apply m.leadingCoeff_binomial
  · intro r _
    convert isRegular_one
    apply leadingCoeff_binomial

/-- The support of `Alon.P S i` is the set of exponents of the form `single i e`,
  for `e ≤ S.card`. -/
private lemma prod_support_le {ι : Type*} (i : ι) (S : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (Alon.P S i).support) :
    ∃ e ≤ S.card, m = single i e := by
  classical
  have hP : Alon.P S i = MvPolynomial.rename (fun (_ : Unit) ↦ i) (Alon.P S ()) := by
    simp [Alon.P, map_prod]
  rw [hP, support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  haveI : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () S.card by
      simpa [MonomialOrder.lex_le_iff_of_unique] using this
    rw [← Alon.degP]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_notin_range, single_eq_of_ne (Ne.symm hj)]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Fintype σ]

open scoped BigOperators

theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R)
      (_ : ∀ i, ((∏ s ∈ S i, (X i - C s)) * h i).totalDegree ≤ f.totalDegree),
    f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h := by
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [Alon.leadingCoeffP, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this, add_zero] at hf
    exact ⟨fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod r (fun i ↦ S i)
  · intro i
    rw [degreeOf_eq_sup, Set.ncard_coe_Finset, Finset.sup_lt_iff (by simp [Sne i])]
    intro c hc
    rw [← not_le]
    intro h'
    apply hr c hc i
    intro j
    rw [Alon.degP, single_apply]
    split_ifs with hj
    · rw [← hj]
      exact h'
    · exact zero_le _
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero]
    rw [linearCombination_apply, map_finsupp_sum, Finsupp.sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert mul_zero _
    rw [Alon.P, map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp only [map_sub, eval_X, eval_C, sub_self]

theorem combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < (S i).card) :
    ∃ (s : σ → R) (_ : ∀ i, s i ∈ S i), eval s f ≠ 0 := by
  letI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  classical
  by_contra Heval
  apply ht
  push_neg at Heval
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i ↦ by rw [← Finset.card_pos]; exact lt_of_le_of_lt (zero_le _) (htS i))
    f Heval
  change f = linearCombination (MvPolynomial σ R) (fun i ↦ Alon.P (S i) i) h at hf
  change ∀ i, (Alon.P (S i) i * h i).totalDegree ≤ _ at hh
  rw [hf]
  rw [linearCombination_apply, Finsupp.sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * Alon.P (S i) i with hg
  by_cases hi : h i = 0
  · simp [hi]
  have : g.totalDegree ≤ f.totalDegree := by
    simp only [hg, mul_comm, hh i]
  -- one could simplify this by proving `totalDegree_mul_eq` (at least in a domain)
  rw [hg, ← degree_degLexDegree,
    degree_mul_of_isRegular_right hi (by simp only [Alon.leadingCoeffP, isRegular_one]),
    Alon.degP, degree_add, degree_degLexDegree, degree_single, ht'] at this
  rw [smul_eq_mul, coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq, ← mem_support_iff]
  intro hq
  obtain ⟨e, _, hq⟩ := prod_support_le _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  change (h i).totalDegree < p.degree
  apply lt_of_add_lt_add_right (a := (S i).card)
  apply lt_of_le_of_lt this
  rw [← hpq, degree_add, add_lt_add_iff_left, hq, degree_single]
  rw [← not_le]
  intro hq'
  apply not_le.mpr (htS i)
  apply le_trans hq'
  simp only [← hpq, hq, coe_add, Pi.add_apply, single_eq_same, le_add_iff_nonneg_left, zero_le]

end MvPolynomial
