/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` :
  if `f` vanishes at any such point and `f.degreeOf s < #(S s)` for all `s`,
  then `f = 0`.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h`,
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

- [Rote, *The Generalized Combinatorial Lasoń-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

public section

open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

namespace MvPolynomial

open Finsupp Function

/-- A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
theorem eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, that] at this
    apply h _ (fun i ↦ S (e i))
    · intro i
      convert! Hdeg (e i)
      conv_lhs => rw [← e.symm_apply_apply i, degreeOf_rename_of_injective e.symm.injective]
    · intro x hx
      simp only [MvPolynomial.eval_rename]
      apply Heval
      intro s
      simp only [Function.comp_apply]
      convert! hx (e.symm s)
      simp only [Equiv.apply_symm_apply]
  | h_empty =>
    suffices P = C (constantCoeff P) by
      specialize Heval default (fun i ↦ PEmpty.elim i)
      rw [this, eval_C] at Heval
      rw [this, Heval, C_0]
    ext m
    suffices m = 0 by simp [this, ← constantCoeff_eq]
    ext d; exact PEmpty.elim d
  | @h_option σ _ h =>
    set Q := optionEquivLeft R σ P with hQ
    suffices Q = 0 by
      rw [← AlgEquiv.symm_apply_apply (optionEquivLeft R σ) P, ← hQ, this, map_zero]
    have Heval' (x : σ → R) (hx : ∀ i, x i ∈ S (some i)) : Polynomial.map (eval x) Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S none)
      · intro y hy
        rw [← optionEquivLeft_elim_eval]
        apply Heval
        simp only [Option.forall, Option.elim_none, hy, Option.elim_some, hx, implies_true,
          and_self]
      · apply lt_of_le_of_lt _ (Hdeg none)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [hQ]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert! map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero]
        set n := (embDomain Function.Embedding.some m).update none d with hn
        rw [eq_option_embedding_update_none_iff] at hn
        rw [← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert! Finset.le_sup hm
        exact hn.1.symm
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by simp only [this, coeff_zero]
    apply h _ (fun i ↦ S (some i))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg (some i))
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      set n := (embDomain Function.Embedding.some e).update none m with hn
      rw [eq_option_embedding_update_none_iff] at hn
      rw [hQ, ← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none, ← ne_eq,
        ← MvPolynomial.mem_support_iff] at he
      convert! Finset.le_sup he
      rw [← hn.2, some_apply]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

open MonomialOrder

/- Here starts the actual proof of the combinatorial Nullstellensatz -/

variable {σ : Type*}

/-- The polynomial in `X i` that vanishes at all elements of `S`. -/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r ∈ S, (X i - C r)

/-- The degree of `Alon.P S i` with respect to `X i` is the cardinality of `S`,
  and `0` otherwise. -/
private theorem Alon.degree_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i #S := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

/-- The leading coefficient of `Alon.P S i` is `1`. -/
private theorem Alon.monic_P (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.Monic (P S i) :=
  Monic.prod (fun r _ ↦ m.monic_X_sub_C i r)

/-- The support of `Alon.P S i` is the set of exponents of the form `single i e`,
  for `e ≤ S.card`. -/
private lemma Alon.of_mem_P_support {ι : Type*} (i : ι) (S : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (Alon.P S i).support) :
    ∃ e ≤ S.card, m = single i e := by
  classical
  have hP : Alon.P S i = .rename (fun _ ↦ i) (Alon.P S ()) := by simp [Alon.P]
  rw [hP, support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  have : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () #S by
      simpa [MonomialOrder.lex_le_iff_of_unique] using this
    rw [← Alon.degree_P]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert! he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_of_notMem_range, single_eq_of_ne hj]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Finite σ]

/-- The **Combinatorial Nullstellensatz**.

If `f` vanishes at every point `x : σ → R` such that `x s ∈ S s` for all `s`,
then it can be written as a linear combination
`f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h`,
for some `h : σ →₀ MvPolynomial σ R` such that
`((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

[Alon_1999], theorem 1. -/
theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R),
      (∀ i, ((∏ s ∈ S i, (X i - C s)) * h i).totalDegree ≤ f.totalDegree) ∧
      f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  suffices hr' : r = 0 by
    rw [hr', add_zero] at hf
    exact ⟨h, fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod_finset r S
  · intro i
    rw [degreeOf_eq_sup, Finset.sup_lt_iff (by simp [Sne i])]
    aesop (add simp [Alon.degree_P])
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero,
      linearCombination_apply, map_finsuppSum, Finsupp.sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert! mul_zero _
    rw [Alon.P, _root_.map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp

/-- The **Combinatorial Nullstellensatz**.

Given a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
`f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

[Alon_1999], theorem 2 -/
theorem combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < #(S i)) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 := by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  by_contra! Heval
  apply ht
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i ↦ by rw [← Finset.card_pos]; exact Nat.zero_lt_of_lt (htS i)) f Heval
  rw [hf]
  rw [linearCombination_apply, Finsupp.sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * Alon.P (S i) i with hg
  by_cases hi : h i = 0
  · simp [hi]
  have : g.totalDegree ≤ f.totalDegree := by
    rw [hg, mul_comm]
    exact hh i
  -- one could simplify this by proving `totalDegree_mul_eq` (at least in a domain)
  rw [hg, ← degree_degLexDegree,
    degree_mul_of_isRegular_right hi (by simp only [(Alon.monic_P ..).leadingCoeff_eq_one,
      isRegular_one]),
    Alon.degree_P, map_add, degree_degLexDegree, degree_single, ht'] at this
  rw [smul_eq_mul, coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq, ← mem_support_iff]
  intro hq
  obtain ⟨e, hq', hq⟩ := Alon.of_mem_P_support _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  rw [← Finsupp.degree_apply]
  apply lt_of_add_lt_add_right (lt_of_le_of_lt this _)
  rw [← hpq, map_add, add_lt_add_iff_left, hq, degree_single]
  apply lt_of_le_of_lt _ (htS i)
  simp [← hpq, hq]

private noncomputable def quotient_remainder (f : MvPolynomial σ R) (i : σ) (r : R) :
    MvPolynomial σ R × MvPolynomial σ R :=
  haveI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  let q :=
    (degLex.div (fun _ ↦ (degLex.monic_X_sub_C i r).leadingCoeff_eq_one ▸ isUnit_one) f).choose
  have hq := 
    (degLex.div
      (fun _ ↦ (degLex.monic_X_sub_C i r).leadingCoeff_eq_one ▸ isUnit_one) f
      (b := fun _ : Unit ↦ X i - C r)).choose_spec
  let r := hq.choose
  ⟨q 0, r⟩

private noncomputable def quotient (f : MvPolynomial σ R) (i : σ) (r : R) :
    MvPolynomial σ R :=
  (quotient_remainder f i r).1

private noncomputable def remainder (f : MvPolynomial σ R) (i : σ) (r : R) :
    MvPolynomial σ R :=
  (quotient_remainder f i r).2

@[simp]
private theorem mul_quotient_add_remainder_eq {f : MvPolynomial σ R} {i : σ} {r : R} :
    quotient f i r * (X i - C r) + remainder f i r = f := by
  sorry

/-- Division of `f` by the monic linear polynomial `X i - C r`: there exist a quotient `g`
and a remainder `h` not involving `X i`. -/
private lemma Alon.exists_eq_mul_X_sub_C_add
    [Nontrivial R] (f : MvPolynomial σ R) (i : σ) (r : R) :
    ∃ g h : MvPolynomial σ R, f = g * (X i - C r) + h ∧ h.degreeOf i = 0 := by
  haveI : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨g, rem, hf, -, hrem⟩ := degLex.div (b := fun _ : Unit ↦ X i - C r)
    (fun _ ↦ (degLex.monic_X_sub_C i r).leadingCoeff_eq_one ▸ isUnit_one) f
  refine ⟨g 0, rem, ?_, ?_⟩
  · rw [hf, linearCombination_unique, smul_eq_mul]
  · rw [← Nat.lt_one_iff, degreeOf_lt_iff Nat.one_pos]
    intro m hm
    rw [Nat.lt_one_iff]
    have hc := hrem m hm ()
    rw [degLex.degree_X_sub_C i r, Finsupp.single_le_iff] at hc
    omega

omit [Finite σ] in
/-- Key recurrence for the coefficients of the quotient `g` in `f = g * (X i - C r) + h`
where `h` does not involve `X i`. -/
private lemma Alon.coeff_recurrence {i : σ} {r : R} {g h f : MvPolynomial σ R}
    (hfgh : f = g * (X i - C r) + h) (hdeg : h.degreeOf i = 0) (m : σ →₀ ℕ) :
    f.coeff (m + single i 1) = g.coeff m - r * g.coeff (m + single i 1) := by
  have hh : h.coeff (m + single i 1) = 0 := by
    by_contra hne
    have hle := monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hne)
    rw [hdeg] at hle
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
    omega
  rw [hfgh, coeff_add, hh, add_zero, mul_sub, coeff_sub, coeff_mul_X, mul_comm g (C r), coeff_C_mul]

omit [Finite σ] in
/-- If `f.coeff (m + single i c) = 0` for all `c > 0`, then `g.coeff m = 0`, where `g` is the
quotient in `f = g * (X i - C r) + h` and `h` does not involve `X i`. -/
private lemma Alon.coeff_quotient_eq_zero {i : σ} {r : R} {g h f : MvPolynomial σ R}
    (hfgh : f = g * (X i - C r) + h) (hdeg : h.degreeOf i = 0)
    (m : σ →₀ ℕ) (hm : ∀ c, 0 < c → f.coeff (m + single i c) = 0) :
    g.coeff m = 0 := by
  have key : ∀ N : ℕ, g.coeff m = r ^ N * g.coeff (m + single i N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ihN =>
      have hrec := Alon.coeff_recurrence hfgh hdeg (m + single i N)
      have he : m + single i N + single i 1 = m + single i (N + 1) := by
        rw [add_assoc, ← single_add]
      rw [he, hm (N + 1) N.succ_pos] at hrec
      have hstep : g.coeff (m + single i N) = r * g.coeff (m + single i (N + 1)) := by
        rw [eq_comm, sub_eq_zero] at hrec; exact hrec
      rw [ihN, hstep]; ring
  rw [key (g.totalDegree + 1)]
  apply mul_eq_zero_of_right
  apply coeff_eq_zero_of_totalDegree_lt
  have hDi : (m + single i (g.totalDegree + 1)) i = m i + (g.totalDegree + 1) := by
    simp [Finsupp.add_apply, Finsupp.single_eq_same]
  have hmem : i ∈ (m + single i (g.totalDegree + 1)).support := by
    rw [Finsupp.mem_support_iff, hDi]; omega
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum (f := fun j ↦ (m + single i (g.totalDegree + 1)) j)
      (fun j _ ↦ Nat.zero_le _) hmem)
  rw [hDi]
  omega

omit [Finite σ] in
/-- Evaluating a polynomial not involving `X i` is unaffected by updating the `i`-th coordinate. -/
private lemma Alon.eval_update_of_degreeOf_eq_zero [DecidableEq σ]
    (h : MvPolynomial σ R) (i : σ) (r : R) (x : σ → R) (hdeg : h.degreeOf i = 0) :
    eval (Function.update x i r) h = eval x h := by
  rw [eval_eq, eval_eq]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  congr 1
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have hji : j ≠ i := by
    have := monomial_le_degreeOf j hd
    grind only [Finsupp.mem_support_iff]
  rw [Function.update_of_ne hji]

/--
Michał Lasoń, A generalization of Combinatorial Nullstellensatz, 2013, Theorem 2
-/
theorem generalized_combinatorial_nullstellensatz
    [IsDomain R] (f : MvPolynomial σ R) (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0)
    (ht' : ∀ t' : σ →₀ ℕ, t < t' → f.coeff t' = 0)
    (S : σ → Finset R) (htS : ∀ ⦃i⦄, t i < #(S i)) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 := by
  classical
  -- Generalize over `f`, `t` and `S` so that the induction hypothesis is usable.
  suffices h : ∀ (n : ℕ) (f : MvPolynomial σ R) (t : σ →₀ ℕ), t.degree = n →
      f.coeff t ≠ 0 → (∀ t' : σ →₀ ℕ, t < t' → f.coeff t' = 0) →
      ∀ (S : σ → Finset R), (∀ i, t i < #(S i)) →
      ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 by
    exact h t.degree f t rfl ht ht' S @htS
  -- A pointwise comparison for `Finsupp`, used repeatedly below.
  intro n
  induction n with
  | zero =>
    intro f t ht htc htmax S hScard
    rw [Finsupp.degree_eq_zero_iff] at ht
    subst ht
    have hf₁ : f = C f.constantCoeff := by
      simp only [coe_zero, Pi.zero_apply, Finset.card_pos] at hScard
      ext t'
      by_cases ht'₀ : t' = 0
      · subst ht'₀
        simp only [constantCoeff_eq, coeff_C, ↓reduceIte]
      · simp only [htmax t' (Ne.pos ht'₀), coeff_C, right_eq_ite_iff]
        rintro rfl
        exact (ht'₀ rfl).elim
    rw [hf₁]
    simp only [coe_zero, Pi.zero_apply, Finset.card_pos] at hScard
    use (hScard · |>.exists_mem.choose)
    simp only [Exists.choose_spec, implies_true, eval_C, true_and]
    tauto
  | succ n ih =>
    intro f t ht htc htmax S hScard
    have htne : t ≠ 0 := by
      rintro rfl
      exact n.succ_ne_zero ht.symm
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr htne
    rw [Finsupp.mem_support_iff] at hi
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hScard i))
    obtain ⟨g, h, hfgh, hdeg⟩ := Alon.exists_eq_mul_X_sub_C_add f i r
    by_cases Hh : ∃ y : σ → R, (∀ j, y j ∈ S j) ∧ eval y h ≠ 0
    · obtain ⟨y, hy, hyh⟩ := Hh
      refine ⟨Function.update y i r, by grind, ?_⟩
      rw [hfgh, map_add, map_mul, map_sub, eval_X, eval_C, Function.update_self, sub_self,
        mul_zero, zero_add, Alon.eval_update_of_degreeOf_eq_zero h i r y hdeg]
      exact hyh
    · simp only [not_exists, not_and, not_not] at Hh
      set t₀ := t - single i 1 with ht₀def
      have hcancel : t₀ + single i 1 = t := ht₀def ▸ Finsupp.sub_add_single_one_cancel hi
      have hdeg₀ : t₀.degree = n := by
        have h2 : t.degree = t₀.degree + 1 := by rw [← hcancel, map_add, Finsupp.degree_single]
        grind only
      have hB : g.coeff t₀ = f.coeff t := by
        have hrec := Alon.coeff_recurrence hfgh hdeg t₀
        have hgt : g.coeff t = 0 := by
          refine Alon.coeff_quotient_eq_zero hfgh hdeg t fun c hc ↦ htmax _ ?_
          refine lt_of_le_of_ne le_self_add fun heq ↦ ?_
          have hcoord := congrArg (fun z : σ →₀ ℕ ↦ z i) heq
          simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hcoord
          grind only
        rw [hcancel, hgt, mul_zero, sub_zero] at hrec
        exact hrec.symm
      have hgmax (u : σ →₀ ℕ) (hu : t₀ < u) : g.coeff u = 0 := by
        refine Alon.coeff_quotient_eq_zero hfgh hdeg u fun c hc ↦ htmax _ ?_
        obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hu
        obtain ⟨j, hj₁⟩ := Finsupp.ne_iff.mp hne
        refine lt_of_le_of_ne ?_ ?_
        · rw [← hcancel]
          exact add_le_add hle (Finsupp.single_le_single.mpr hc)
        · rintro rfl
          have hj₂ : t₀ j < u j := lt_of_le_of_ne (hle _) hj₁
          have htj : (u + single i c) j = t₀ j + (single i 1) j := by
            rw [← hcancel, Finsupp.add_apply]
          simp only [coe_add, Pi.add_apply] at htj
          grind only [single_apply]
      set S' : σ → Finset R := Function.update S i ((S i).erase r) with hS'def
      have hScard' (j : σ) : t₀ j < #(S' j) := by
        grind only [tsub_apply, Function.update, single_apply, Finset.card_erase_of_mem]
      obtain ⟨s, hs, hsg⟩ := ih g t₀ hdeg₀ (hB ▸ htc) hgmax S' hScard'
      have hsS : ∀ j, s j ∈ S j := by grind
      refine ⟨s, hsS, ?_⟩
      rw [hfgh, map_add, map_mul, map_sub, eval_X, eval_C, Hh s hsS, add_zero]
      refine mul_ne_zero hsg (sub_ne_zero.mpr ?_)
      have hmem := hS'def ▸ hs i
      rw [Function.update_self] at hmem
      exact (Finset.mem_erase.mp hmem).1

end MvPolynomial
